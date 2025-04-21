# 🌀 BWTree‑RS

*A latch‑free, cache‑friendly, fully in‑memory Bw‑tree for Rust.*

> "One CAS per write, zero latches, millions of ops per second."

BW-trees provide high concurrency and performance for modern multi-core systems.

> Note: very very WIP

---

## ✨ Features

| ✅ | Description |
|----|-------------|
| **Latch‑free** | All structural changes use a single `compare_exchange` on the mapping table. |
| **Epoch‑based GC** | Memory is reclaimed safely with `crossbeam_epoch`; no hazards, no ABA. |
| **Ordered + concurrent** | Point look‑ups match hash‑map speed while range scans are linear‑time. |
| **Familiar API** | `BwTreeMap` API matches the standard library's `BTreeMap` |
| **Pluggable value type** | Any `Send + Sync + 'static` payload via generic `K` and `V`. |
| **No `unsafe` in public API** | Internals use minimal `unsafe` blocks for raw pointers. |

* Implemented operations:
  * `insert`: Add key-value pairs
  * `get`: Retrieve values by key

---

## 📦 Getting started

```bash
cargo add bwtree --git https://github.com/willothy/bwtree-rs
```

```rust
use bwtree::BwTreeMap;

let map = BwTreeMap::new();

// writers
map.insert(42, "life");
map.insert(7,  "lucky");

// readers
assert_eq!(map.get(&42, &guard), Some("life"));
```

---

## 🏗️ Architecture snapshot

```
      MappingTable                 Page 0
     ┌─┬─────────────────┐
  PID│0│ AtomicPtr<Page> ├───────► Page::Delta(DeltaEntry {
     ├─┼─────────────────┤             delta: Delta::Insert {
  ┌─►│1│ AtomicPtr<Page> │                 k: ..., v: ...
  │  ├─┼─────────────────┤             },
  │  │2│ <uninit>        │             next: AtomicPtr<Page> ──┐
  │  └─┴─────────────────┘         })                          │
  │                                                            │
  │┌───────────────────────────────────────────────────────────┘
  ││
  │└►Page::Delta(DeltaEntry {          ┌─► Page::BaseLeaf(entries...)
  │      delta: Delta::SplitChild {    │
  │          separator: K,             │
  │          right: PID(1),─────────┐  │
  │      },                         │  │
  │      next: AtomicPtr<Page> ─────┼──┘
  │  })                             │
  │                                 │
  └─────────────────────────────────┘

```

* **Single CAS = serialisation**
  Every update prepends a *delta* node and installs it with `compare_exchange`.
* **Side links & helper rule**
  Incomplete splits/merges are finished by the thread that sees them → lock‑free progress. (TODO)
* **Epoch GC**
  Freed nodes are reclaimed once no active thread can still reach them.

---

## 🚧 To Do

* Implement page consolidation
* Add range queries
* Implement page splitting for large pages
* Add merge operations for sparse pages
* Benchmarking against other concurrent data structures

## 📚 References

* [The Bw-Tree: A B-tree for New Hardware Platforms (Microsoft Research)](https://15721.courses.cs.cmu.edu/spring2018/papers/08-oltpindexes1/bwtree-icde2013.pdf)
* [Building a Bw-Tree Takes More Than Just Buzz Words (CMU)](https://db.cs.cmu.edu/papers/2018/mod342-wangA.pdf)
  * Video talk [here](https://www.youtube.com/watch?v=UxuFL8dgiEw)

## 📊 Visualization

This implementation includes a visualization module that can generate Graphviz DOT files to help understand the structure and behavior of the BwTree.

### Requirements

- [Graphviz](https://graphviz.org/) must be installed to generate PNG/SVG files from DOT files

### Usage

#### Visualizing a BwTree

```rust
use bwtree::{BwTreeMap, visualization::BwTreeVisualize};

// Create a BwTree
let tree = BwTreeMap::<i32, String>::new();

// Add some data
tree.insert(1, "one".to_string());
tree.insert(2, "two".to_string());
tree.insert(3, "three".to_string());

// Generate DOT representation as a string
let dot_code = tree.visualize();

// Or save directly to a file
tree.save_visualization("my_bwtree.dot").unwrap();

// Convert DOT to an image if you have GraphViz installed
bwtree::visualization::generate_image("my_bwtree.dot", "my_bwtree.png").unwrap();
```

#### Running the Example

```
cargo run --example visualize [output_file.dot]
```

This will:
1. Create a BwTree
2. Populate it with sample data
3. Generate a DOT file visualization
4. Attempt to create a PNG image using GraphViz (if installed)

#### Understanding the Visualization

The visualization uses colors and shapes to represent different node types:

- **Light blue boxes**: Base leaf nodes containing key-value pairs
- **Light green boxes**: Base index nodes containing key-pid pairs
- **Light yellow ellipses**: Delta nodes (Insert, Delete, SplitChild, IndexEntry)

Edges represent relationships between nodes:
- **next**: Links between delta nodes in a delta chain
- **right**: Links to right siblings in split operations
- **idx=X**: Links from index nodes to their children

## 📜 License (Apache-2.0)

Copyright 2025 Will Hopkins

Licensed under the Apache License, Version 2.0 (the "License");

you may not use this file except in compliance with the License.

You may obtain a copy of the License at

<http://www.apache.org/licenses/LICENSE-2.0>

Unless required by applicable law or agreed to in writing, software

distributed under the License is distributed on an "AS IS" BASIS,

WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.

See the License for the specific language governing permissions and

limitations under the License.