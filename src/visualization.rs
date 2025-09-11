use std::collections::HashMap;
use std::fmt::{self, Display};
use std::fs::File;
use std::io::Write;
use std::ops::Deref;
use std::path::Path;

use crate::{BwTreeMap, Delta, DeltaEntry, Page, PID};
use crossbeam::epoch::{Guard, Shared};
use dot::{Edges, GraphWalk, Id, LabelText, Labeller, Nodes};

/// A struct to hold the BwTree's data needed for visualization
pub struct BwTreeGraph<'a, K: Display + Ord + PartialEq + Clone + 'static, V: Display + Clone> {
    tree: &'a BwTreeMap<K, V>,
    guard: &'a Guard,
    nodes: Vec<NodeData<'a, K, V>>,
    edges: Vec<EdgeData>,
    // Track which nodes we've already processed
    node_indices: HashMap<NodeId, usize>, // NodeId -> index in nodes vector
}

/// A unique identifier for a node in the visualization
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct NodeId {
    // The page ID
    pid: usize,
    // Position in the delta chain (0 = top of chain)
    chain_pos: usize,
}

/// Metadata for a node in the visualization
struct NodeData<'a, K: Display, V: Display> {
    id: NodeId,
    node_type: NodeType,
    page: Shared<'a, Page<K, V>>,
    label: String,
}

/// Edge between two nodes in the visualization
struct EdgeData {
    source: NodeId,
    target: NodeId,
    label: String,
}

/// Types of nodes in the BwTree
enum NodeType {
    BaseLeaf,
    BaseIndex,
    Delta,
}

impl<'a, K, V> BwTreeGraph<'a, K, V>
where
    K: Display + Ord + PartialEq + Clone + 'static,
    V: Display + Clone,
{
    /// Create a new BwTreeGraph from a BwTreeMap
    pub fn new(tree: &'a BwTreeMap<K, V>, guard: &'a Guard) -> Self {
        let mut graph = Self {
            tree,
            guard,
            nodes: Vec::new(),
            edges: Vec::new(),
            node_indices: HashMap::new(),
        };

        // Start with the root node (PID 0, position 0)
        let root_id = NodeId {
            pid: tree.root().0,
            chain_pos: 0,
        };
        graph.process_chain(root_id.pid);

        graph
    }

    /// Generate the DOT representation of the graph
    pub fn to_dot(&self) -> String {
        let mut output = Vec::new();
        dot::render(self, &mut output).unwrap();
        String::from_utf8(output).unwrap()
    }

    /// Save the DOT representation to a file
    pub fn save_dot<P: AsRef<Path>>(&self, path: P) -> std::io::Result<()> {
        let dot_string = self.to_dot();
        let mut file = File::create(path)?;
        file.write_all(dot_string.as_bytes())?;
        Ok(())
    }

    /// Process an entire delta chain starting from a specific PID
    fn process_chain(&mut self, pid: usize) -> usize {
        // Process the head node (chain_pos = 0)
        let head_id = NodeId { pid, chain_pos: 0 };
        let head_idx = self.process_node(head_id);

        // Connect to any referenced nodes (SplitChild, IndexEntry) and their chains
        let head_ptr = self.tree.load(PID(pid), &self.guard);
        self.follow_references(head_id, head_ptr);

        head_idx
    }

    /// Follow references from a node to other chains (SplitChild, IndexEntry)
    fn follow_references(&mut self, node_id: NodeId, ptr: Shared<'a, Page<K, V>>) {
        let page = unsafe { &*ptr.as_raw() };

        match page {
            Page::Delta { delta, next } => {
                match delta {
                    Delta::SplitChild { right, .. } | Delta::IndexEntry { right, .. } => {
                        // Process the referenced chain if not already processed
                        let target_id = NodeId {
                            pid: right.0,
                            chain_pos: 0,
                        };
                        if !self.node_indices.contains_key(&target_id) {
                            self.process_chain(right.0);
                        }

                        // Create an edge to the referenced chain
                        let target_idx = self.node_indices[&target_id];
                        self.edges.push(EdgeData {
                            source: node_id,
                            target: target_id,
                            label: "right".to_string(),
                        });
                    }
                    _ => {}
                }

                // Follow the next pointer in this chain
                let next_ptr = next.load(std::sync::atomic::Ordering::Acquire, &self.guard);
                let next_id = NodeId {
                    pid: node_id.pid,
                    chain_pos: node_id.chain_pos + 1,
                };
                if !self.node_indices.contains_key(&next_id) {
                    let next_idx = self.process_node(next_id);
                    self.follow_references(next_id, next_ptr);

                    // Create an edge to the next node in the chain
                    self.edges.push(EdgeData {
                        source: node_id,
                        target: next_id,
                        label: "next".to_string(),
                    });
                }
            }
            Page::BaseIndex { entries, .. } => {
                // Process all children in the index
                for (idx, (_, child_pid)) in entries.iter().enumerate() {
                    let child_id = NodeId {
                        pid: child_pid.0,
                        chain_pos: 0,
                    };
                    if !self.node_indices.contains_key(&child_id) {
                        self.process_chain(child_pid.0);
                    }

                    // Create edges to all children
                    self.edges.push(EdgeData {
                        source: node_id,
                        target: child_id,
                        label: format!("idx={}", idx),
                    });
                }
            }
            _ => {}
        }
    }

    /// Process a single node and add it to the graph
    fn process_node(&mut self, node_id: NodeId) -> usize {
        // If we've already processed this node, return its index
        if let Some(&idx) = self.node_indices.get(&node_id) {
            return idx;
        }

        // Get the page from the tree
        let pid = PID(node_id.pid);
        let ptr = self.tree.load(pid, &self.guard);

        // Find the correct node in the delta chain
        let mut current_ptr = ptr;
        let mut chain_pos = 0;

        while chain_pos < node_id.chain_pos {
            match unsafe { &*current_ptr.as_raw() } {
                Page::Delta { next, .. } => {
                    current_ptr = next.load(std::sync::atomic::Ordering::Acquire, &self.guard);
                    chain_pos += 1;
                }
                _ => break, // Reached a base page
            }
        }

        let idx = self.nodes.len();
        self.node_indices.insert(node_id, idx);

        // Process the node based on its type
        let page = unsafe { &*current_ptr.as_raw() };
        match page {
            Page::BaseLeaf {
                entries: items,
                side_link,
            } => {
                let label = format!(
                    "BaseLeaf\nPID={}, chain_pos={}\nSIDE_LINK={} ({} count)\n{}",
                    node_id.pid,
                    node_id.chain_pos,
                    side_link
                        .map(|l| l.0.to_string())
                        .unwrap_or_else(|| "none".to_string()),
                    items.len(),
                    self.format_items(items.as_slice())
                );
                self.nodes.push(NodeData {
                    id: node_id,
                    node_type: NodeType::BaseLeaf,
                    page: current_ptr,
                    label,
                });
                if let Some(side_link) = side_link {
                    self.edges.push(EdgeData {
                        source: node_id,
                        target: NodeId {
                            pid: side_link.0,
                            chain_pos: 0,
                        },
                        label: "side_link".to_owned(),
                    })
                }
            }
            Page::BaseIndex {
                entries: items,
                side_link,
            } => {
                let label = format!(
                    "BaseIndex\nPID={}, chain_pos={}\nSIDE_LINK={} ({} count)\n{}",
                    node_id.pid,
                    node_id.chain_pos,
                    side_link
                        .map(|l| l.0.to_string())
                        .unwrap_or_else(|| "none".to_string()),
                    items.len(),
                    self.format_index_items(items.as_slice())
                );
                self.nodes.push(NodeData {
                    id: node_id,
                    node_type: NodeType::BaseIndex,
                    page: current_ptr,
                    label,
                });
            }
            Page::Delta { delta, .. } => {
                let label = match delta {
                    Delta::Insert { key, value } => {
                        format!(
                            "Delta::Insert\nPID={}, chain_pos={}\nkey={}, value={}",
                            node_id.pid, node_id.chain_pos, key, value
                        )
                    }
                    Delta::Delete { key } => {
                        format!(
                            "Delta::Delete\nPID={}, chain_pos={}\nkey={}",
                            node_id.pid, node_id.chain_pos, key
                        )
                    }
                    Delta::SplitChild { separator, right } => {
                        format!(
                            "Delta::SplitChild\nPID={}, chain_pos={}\nsep={}, right={}",
                            node_id.pid, node_id.chain_pos, separator, right.0
                        )
                    }
                    Delta::IndexEntry { separator, right } => {
                        format!(
                            "Delta::IndexEntry\nPID={}, chain_pos={}\nsep={}, right={}",
                            node_id.pid, node_id.chain_pos, separator, right.0
                        )
                    }
                };

                self.nodes.push(NodeData {
                    id: node_id,
                    node_type: NodeType::Delta,
                    page: current_ptr,
                    label,
                });
            }
        }

        idx
    }

    /// Format items for display in a node label
    fn format_items(&self, items: &[(K, V)]) -> String {
        if items.is_empty() {
            return "[empty]".to_string();
        }

        let mut result = String::new();
        for (i, (k, v)) in items.iter().enumerate() {
            if i > 5 {
                result.push_str("...");
                break;
            }
            result.push_str(&format!("{}:{}", k, v));
            if i < items.len() - 1 && i < 5 {
                result.push_str(", ");
            }
        }
        result
    }

    /// Format index items for display in a node label
    fn format_index_items(&self, items: &[(K, PID)]) -> String {
        if items.is_empty() {
            return "[empty]".to_string();
        }

        let mut result = String::new();
        for (i, (k, pid)) in items.iter().enumerate() {
            if i > 5 {
                result.push_str("...");
                break;
            }
            result.push_str(&format!("{}:PID({})", k, pid.0));
            if i < items.len() - 1 && i < 5 {
                result.push_str(", ");
            }
        }
        result
    }
}

type Node = usize;
type Edge = (usize, usize, String);

impl<'a, K, V> Labeller<'a, usize, (usize, usize, String)> for BwTreeGraph<'a, K, V>
where
    K: Display + Ord + PartialEq + Clone + 'static,
    V: Display + Clone,
{
    fn graph_id(&'a self) -> Id<'a> {
        Id::new("bwtree").unwrap()
    }

    fn node_id(&'a self, n: &Node) -> Id<'a> {
        Id::new(format!("node{}", n)).unwrap()
    }

    fn node_label(&'a self, n: &Node) -> LabelText<'a> {
        LabelText::LabelStr(self.nodes[*n].label.clone().into())
    }

    fn edge_label(&'a self, e: &Edge) -> LabelText<'a> {
        LabelText::LabelStr(e.2.clone().into())
    }

    fn node_style(&'a self, n: &Node) -> dot::Style {
        match self.nodes[*n].node_type {
            NodeType::BaseLeaf => dot::Style::Filled,
            NodeType::BaseIndex => dot::Style::Filled,
            NodeType::Delta => dot::Style::Filled,
        }
    }

    fn node_color(&'a self, n: &Node) -> Option<dot::LabelText<'a>> {
        match self.nodes[*n].node_type {
            NodeType::BaseLeaf => Some(LabelText::LabelStr("lightblue".into())),
            NodeType::BaseIndex => Some(LabelText::LabelStr("lightgreen".into())),
            NodeType::Delta => Some(LabelText::LabelStr("lightyellow".into())),
        }
    }

    fn node_shape(&'a self, n: &Node) -> Option<dot::LabelText<'a>> {
        match self.nodes[*n].node_type {
            NodeType::BaseLeaf => Some(LabelText::LabelStr("box".into())),
            NodeType::BaseIndex => Some(LabelText::LabelStr("box".into())),
            NodeType::Delta => Some(LabelText::LabelStr("ellipse".into())),
        }
    }
}

impl<'a, K, V> GraphWalk<'a, Node, Edge> for BwTreeGraph<'a, K, V>
where
    K: Display + Ord + PartialEq + Clone + 'static,
    V: Display + Clone,
{
    fn nodes(&'a self) -> Nodes<'a, Node> {
        (0..self.nodes.len()).collect()
    }

    fn edges(&'a self) -> Edges<'a, Edge> {
        self.edges
            .iter()
            .map(|e| {
                // Map NodeId to indices in nodes Vec
                let source_idx = self.node_indices[&e.source];
                let target_idx = self.node_indices[&e.target];
                (source_idx, target_idx, e.label.clone())
            })
            .collect()
    }

    fn source(&'a self, edge: &Edge) -> Node {
        edge.0
    }

    fn target(&'a self, edge: &Edge) -> Node {
        edge.1
    }
}

/// Extension trait to add visualization methods to BwTreeMap
pub trait BwTreeVisualize<K, V>
where
    K: Display + Ord + PartialEq + Clone + 'static,
    V: Display + Clone,
{
    /// Create a visualization of the BwTree in DOT format
    fn visualize(&self) -> String;

    /// Save a visualization of the BwTree to a DOT file
    fn save_visualization<P: AsRef<Path>>(&self, path: P) -> std::io::Result<()>;
}

impl<K, V> BwTreeVisualize<K, V> for BwTreeMap<K, V>
where
    K: Display + Ord + PartialEq + Clone + 'static,
    V: Display + Clone,
{
    fn visualize(&self) -> String {
        let pin = crossbeam::epoch::pin();
        let graph = BwTreeGraph::new(self, &pin);
        graph.to_dot()
    }

    fn save_visualization<P: AsRef<Path>>(&self, path: P) -> std::io::Result<()> {
        let pin = crossbeam::epoch::pin();
        let graph = BwTreeGraph::new(self, &pin);
        graph.save_dot(path)
    }
}

/// Helper function to create an example BwTree and visualize it
pub fn create_example() -> std::io::Result<String> {
    let tree = BwTreeMap::<i32, String>::new();

    // Insert some values to create different node types
    for i in 1..20 {
        tree.insert(i, format!("value_{}", i));

        // Delete some values to create delete deltas
        if i % 5 == 0 {
            tree.delete(i - 2);
        }
    }

    // Create the visualization
    let dot_graph = tree.visualize();

    // Save to a file
    tree.save_visualization("bwtree_visualization.dot")?;

    Ok(dot_graph)
}

/// Helper function to run the DOT file through GraphViz to generate an image
pub fn generate_image<P: AsRef<Path>>(dot_path: P, output_path: P) -> std::io::Result<()> {
    use std::process::Command;

    Command::new("dot")
        .args([
            "-Tpng",
            dot_path.as_ref().to_str().unwrap(),
            "-o",
            output_path.as_ref().to_str().unwrap(),
        ])
        .output()?;

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_visualization() {
        let tree = BwTreeMap::<i32, String>::new();

        // Insert some values
        tree.insert(1, "one".to_string());
        tree.insert(2, "two".to_string());
        tree.insert(3, "three".to_string());

        // Get the DOT representation
        let dot = tree.visualize();

        // Verify it contains the expected nodes
        assert!(dot.contains("bwtree"));
        assert!(dot.contains("BaseLeaf"));

        // Optionally save to a file
        // tree.save_visualization("test_tree.dot").unwrap();
    }
}

