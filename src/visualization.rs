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
    pid_to_node_id: HashMap<usize, usize>,
}

struct NodeData<'a, K: Display, V: Display> {
    id: usize,
    pid: PID,
    node_type: NodeType,
    page: Shared<'a, Page<K, V>>,
    label: String,
}

struct EdgeData {
    source: usize,
    target: usize,
    label: String,
}

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
            pid_to_node_id: HashMap::new(),
        };

        // Start with the root node (PID 0)
        graph.traverse_from_pid(tree.root());

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

    /// Helper function to traverse and build the graph from a specific PID
    fn traverse_from_pid(&mut self, pid: PID) -> usize {
        // If we've already processed this PID, return its node ID
        if let Some(&node_id) = self.pid_to_node_id.get(&pid.0) {
            return node_id;
        }

        let ptr = self.tree.load(pid, &self.guard);
        let node_id = self.nodes.len();
        self.pid_to_node_id.insert(pid.0, node_id);

        // Process the node based on its type
        let page = unsafe { &*ptr.as_raw() };
        match page {
            Page::BaseLeaf { entries: items, .. } => {
                let label = format!(
                    "BaseLeaf PID={}\n{}",
                    pid.0,
                    self.format_items(items.as_slice())
                );
                self.nodes.push(NodeData {
                    id: node_id,
                    pid,
                    node_type: NodeType::BaseLeaf,
                    page: ptr,
                    label,
                });
            }
            Page::BaseIndex { entries: items, .. } => {
                let label = format!(
                    "BaseIndex PID={}\n{}",
                    pid.0,
                    self.format_index_items(items.as_slice())
                );
                self.nodes.push(NodeData {
                    id: node_id,
                    pid,
                    node_type: NodeType::BaseIndex,
                    page: ptr,
                    label,
                });

                // Add edges to all children
                for (idx, (_key, child_pid)) in items.iter().enumerate() {
                    let child_node_id = self.traverse_from_pid(*child_pid);
                    self.edges.push(EdgeData {
                        source: node_id,
                        target: child_node_id,
                        label: format!("idx={}", idx),
                    });
                }
            }
            Page::Delta { delta, next } => {
                // Process this delta node
                self.process_delta(pid, ptr, node_id, delta);

                // Follow the delta chain
                let next_ptr = next.load(std::sync::atomic::Ordering::Acquire, &self.guard);
                let next_node_id = self.nodes.len();

                // Add next node
                self.process_next_node(next_ptr, next_node_id);

                // Add edge to next node in delta chain
                self.edges.push(EdgeData {
                    source: node_id,
                    target: next_node_id,
                    label: "next".to_string(),
                });
            }
        }

        node_id
    }

    /// Process a delta node and add it to the graph
    fn process_delta(
        &mut self,
        pid: PID,
        ptr: Shared<'a, Page<K, V>>,
        node_id: usize,
        delta: &Delta<K, V>,
    ) {
        let label = match &delta {
            Delta::Insert { key, value } => {
                format!("Delta::Insert PID={}\nkey={}, value={}", pid.0, key, value)
            }
            Delta::Delete { key } => {
                format!("Delta::Delete PID={}\nkey={}", pid.0, key)
            }
            Delta::SplitChild { separator, right } => {
                let right_node_id = self.traverse_from_pid(*right);
                self.edges.push(EdgeData {
                    source: node_id,
                    target: right_node_id,
                    label: "right".to_string(),
                });
                format!(
                    "Delta::SplitChild PID={}\nsep={}, right={}",
                    pid.0, separator, right.0
                )
            }
            Delta::IndexEntry { separator, right } => {
                let right_node_id = self.traverse_from_pid(*right);
                self.edges.push(EdgeData {
                    source: node_id,
                    target: right_node_id,
                    label: "right".to_string(),
                });
                format!(
                    "Delta::IndexEntry PID={}\nsep={}, right={}",
                    pid.0, separator, right.0
                )
            }
        };

        self.nodes.push(NodeData {
            id: node_id,
            pid,
            node_type: NodeType::Delta,
            page: ptr,
            label,
        });
    }

    /// Process the next node in a delta chain
    fn process_next_node(&mut self, ptr: Shared<'a, Page<K, V>>, node_id: usize) {
        let page = unsafe { &*ptr.as_raw() };
        match page {
            Page::BaseLeaf { entries: items, .. } => {
                let label = format!("BaseLeaf\n{}", self.format_items(items.as_slice()));
                self.nodes.push(NodeData {
                    id: node_id,
                    pid: PID(0), // Temporary PID, not a real one
                    node_type: NodeType::BaseLeaf,
                    page: ptr,
                    label,
                });
            }
            Page::BaseIndex { entries: items, .. } => {
                let label = format!("BaseIndex\n{}", self.format_index_items(items.as_slice()));
                self.nodes.push(NodeData {
                    id: node_id,
                    pid: PID(0), // Temporary PID, not a real one
                    node_type: NodeType::BaseIndex,
                    page: ptr,
                    label,
                });

                // We won't follow the children here to avoid circular references
            }
            Page::Delta { delta, next } => {
                // Process this delta node
                self.process_delta(PID(0), ptr, node_id, delta);

                // Follow the delta chain
                let next_ptr = next.load(std::sync::atomic::Ordering::Acquire, &self.guard);
                let next_node_id = self.nodes.len();

                // Add next node
                self.process_next_node(next_ptr, next_node_id);

                // Add edge to next node in delta chain
                self.edges.push(EdgeData {
                    source: node_id,
                    target: next_node_id,
                    label: "next".to_string(),
                });
            }
        }
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
    // type Node = usize;
    // type Edge = (usize, usize, String);

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
            .map(|e| (e.source, e.target, e.label.clone()))
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

