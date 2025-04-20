use std::ops::Deref;

use arc_slice::ArcSlice;
use crossbeam::epoch::{Atomic, CompareExchangeError, Owned, Shared};

mod arc_slice;

#[derive(Debug, Clone, Copy)]
struct PID(usize);

#[repr(C)]
enum Delta<K, V> {
    Insert { key: K, value: V },
    Delete { key: K },

    SplitChild { separator: K, right: PID },
    IndexEntry { separator: K, right: PID },
    // MergeSibling { separator: K, right: PID },
}

#[repr(C)]
struct DeltaEntry<K, V> {
    delta: Delta<K, V>,
    next: Atomic<Page<K, V>>,
}

#[repr(C)]
enum Page<K, V> {
    BaseLeaf(ArcSlice<(K, V)>),
    BaseIndex(ArcSlice<(K, PID)>),
    Delta(DeltaEntry<K, V>),
}

const ROOT_PID: PID = PID(0);
const MAX_BASE: usize = 512;

#[derive(Debug)]
pub struct Ref<'a, K, V> {
    _guard: crossbeam::epoch::Guard,
    key: &'a K,
    value: &'a V,
}

impl<'a, K, V> Ref<'a, K, V> {
    pub fn key(&self) -> &'a K {
        self.key
    }

    pub fn value(&self) -> &'a V {
        self.value
    }
}
impl<'a, K, V> Deref for Ref<'a, K, V> {
    type Target = &'a V;

    fn deref(&self) -> &Self::Target {
        &self.value
    }
}

/// Return `true`   if `(sep → right_pid)` is already visible in `parent_head`.
/// Return `false`  otherwise.
fn has_index_entry<'a, K: Ord, V>(
    mut head: Shared<'a, Page<K, V>>,
    sep: &K, // KP of the split
    guard: &'a crossbeam::epoch::Guard,
) -> bool {
    // Scan the delta chain first (cheap):
    loop {
        match unsafe { &*head.as_raw() } {
            Page::Delta(DeltaEntry {
                delta: Delta::IndexEntry { separator: s, .. },
                next: _,
            }) if s == sep => return true,
            Page::Delta(d) => {
                // next delta
                head = d.next.load(std::sync::atomic::Ordering::Relaxed, &guard)
            }
            Page::BaseIndex(items) => {
                // Fallback: binary search the consolidated base page.
                // items is sorted by separator key.
                return items.binary_search_by_key(&sep, |(k, _)| k).is_ok();
            }
            Page::BaseLeaf(_) => unreachable!("parent is never a leaf"),
        }
    }
}

pub struct BwTreeMap<K, V> {
    slots: boxcar::Vec<Atomic<Page<K, V>>>,
}

impl<K: Ord + PartialEq + Clone + 'static, V: Clone> BwTreeMap<K, V> {
    pub fn new() -> Self {
        let slots = boxcar::Vec::with_capacity(4);

        // Root page
        slots.push(Atomic::new(Page::BaseLeaf(ArcSlice::empty())));

        Self { slots }
    }

    pub fn insert<'a>(&self, key: K, value: V) {
        let guard = crossbeam::epoch::pin();
        let mut stack = Vec::new();
        let pid = self.find_leaf(ROOT_PID, &key, &mut stack, &guard);

        let mut delta = Owned::new(Page::Delta(DeltaEntry {
            delta: Delta::Insert { key, value },
            // We should never actually read this null pointer
            next: Atomic::null(),
        }));

        let mut head = self.load(pid, &guard);
        loop {
            match &*delta {
                Page::Delta(DeltaEntry { next, .. }) => {
                    // Update the next pointer to point to the current head.
                    //
                    // This is necessary so that we can avoid reallocating the delta entry
                    // on every iteration.
                    next.store(head, std::sync::atomic::Ordering::Release);
                }
                _ => unreachable!(),
            }

            match self.slots[pid.0].compare_exchange(
                head,
                delta,
                std::sync::atomic::Ordering::AcqRel,
                std::sync::atomic::Ordering::Relaxed,
                &guard,
            ) {
                Ok(_) => {
                    break;
                }
                Err(CompareExchangeError { new, current }) => {
                    // Avoid cloning the delta on every iteration
                    delta = new;

                    head = current;
                }
            }
        }

        let parent = stack.pop().unwrap();

        self.maybe_consolidate(pid, parent, &guard);
    }

    pub fn get<'a>(&self, key: &K) -> Option<Ref<'a, K, V>> {
        let guard = crossbeam::epoch::pin();
        if let Some((k, v)) =
            self.find_in_slot(ROOT_PID, key, unsafe { std::mem::transmute(&guard) })
        {
            Some(Ref {
                _guard: guard,
                key: k,
                value: v,
            })
        } else {
            None
        }
    }

    pub fn delete<'a>(&self, key: K) {
        let guard = crossbeam::epoch::pin();

        let mut stack = Vec::new();
        let pid = self.find_leaf(ROOT_PID, &key, &mut stack, &guard);

        let mut delta = Owned::new(Page::Delta(DeltaEntry {
            delta: Delta::Delete { key },
            // We should never actually read this null pointer
            next: Atomic::null(),
        }));

        let mut head = self.load(pid, &guard);
        loop {
            match &*delta {
                Page::Delta(DeltaEntry { next, .. }) => {
                    // Update the next pointer to point to the current head.
                    //
                    // This is necessary so that we can avoid reallocating the delta entry
                    // on every iteration.
                    next.store(head, std::sync::atomic::Ordering::Release);
                }
                _ => unreachable!(),
            }

            match self.slots[pid.0].compare_exchange(
                head,
                delta,
                std::sync::atomic::Ordering::AcqRel,
                std::sync::atomic::Ordering::Relaxed,
                &guard,
            ) {
                Ok(_) => {
                    break;
                }
                Err(CompareExchangeError { new, current }) => {
                    // Avoid cloning the delta on every iteration
                    delta = new;

                    head = current;
                }
            }
        }

        self.maybe_consolidate(pid, stack.pop().unwrap(), &guard);
    }

    fn maybe_consolidate(&self, pid: PID, parent_pid: PID, guard: &crossbeam::epoch::Guard) {
        enum Op<'a, K, V> {
            Insert { key: &'a K, value: &'a V },
            Delete { key: &'a K },
        }

        let mut ops = vec![];

        let mut ptr = self.load(pid, guard);
        let mut len = 0;
        while let Page::Delta(delta) = unsafe { &*ptr.as_raw() } {
            len += 1;
            // We need to preserve the order of operations, but don't want to
            // traverse the delta chain twice.
            match &delta.delta {
                Delta::Insert { key, value } => {
                    ops.push(Op::Insert { key, value });
                }
                Delta::Delete { key } => {
                    ops.push(Op::Delete { key });
                }
                _ => {}
            }
            ptr = delta.next.load(std::sync::atomic::Ordering::Acquire, guard);
        }

        if len <= 8 {
            return;
        }

        let base = match unsafe { &*ptr.as_raw() } {
            Page::BaseLeaf(items) => items,
            _ => return, // someone beat us
        };
        let base_ptr = ptr;

        let mut base_items = base.to_vec();
        for op in ops.into_iter().rev() {
            match op {
                Op::Insert { key, value } => {
                    let idx = match base_items.binary_search_by_key(&key, |(k, _)| k) {
                        Ok(i) | Err(i) => i,
                    };
                    base_items.insert(idx, (key.clone(), value.clone()));
                }
                Op::Delete { key } => {
                    if let Ok(idx) = base_items.binary_search_by_key(&key, |(k, _)| k) {
                        base_items.remove(idx);
                    };
                }
            }
        }

        let len = base_items.len();
        let new_base = Owned::new(Page::BaseLeaf(ArcSlice::from_vec(base_items)));
        match self.slots[pid.0].compare_exchange(
            base_ptr,
            new_base,
            std::sync::atomic::Ordering::AcqRel,
            std::sync::atomic::Ordering::Relaxed,
            guard,
        ) {
            Ok(_) => {
                // We successfully consolidated the page.
                // Now we need to check if we need to split the parent.
                if len > MAX_BASE {
                    while let Err(_) = self.split_base(pid, parent_pid) {}
                }
            }
            Err(_) => {
                // Someone else beat us to it.
                // We don't need to do anything here.
            }
        }
    }

    fn split_base(&self, pid: PID, parent_pid: PID) -> Result<(), ()> {
        let guard = crossbeam::epoch::pin();

        let node = self.load(pid, &guard);
        let page = unsafe { &*node.as_raw() };

        match page {
            Page::BaseLeaf(items) => {
                let mid = items.len() / 2;
                let separator = items[mid].0.clone();

                let right = items.slice(mid..);

                let right_pid = PID(self.slots.push(Atomic::new(Page::BaseLeaf(right))));

                let delta = Owned::new(Page::Delta(DeltaEntry::<K, V> {
                    delta: Delta::SplitChild {
                        separator: separator.clone(),
                        right: right_pid,
                    },
                    next: Atomic::from(node),
                }));

                match self.slots[pid.0].compare_exchange(
                    node,
                    delta,
                    std::sync::atomic::Ordering::AcqRel,
                    std::sync::atomic::Ordering::Relaxed,
                    &guard,
                ) {
                    Ok(_) => {
                        // Any search landing in `pid` with `key >= separator` will now follow
                        // the side-link to `right_pid` and still find the correct record.
                    }
                    Err(_) => {
                        // We lost the race - someone else split the page
                        //
                        // retry
                        return Err(());
                    }
                }

                let mut parent_head = self.load(parent_pid, &guard);
                let mut idx_delta = Owned::new(Page::Delta(DeltaEntry::<K, V> {
                    delta: Delta::IndexEntry {
                        separator: separator.clone(),
                        right: right_pid,
                    },
                    next: Atomic::from(parent_head),
                }));

                loop {
                    match self.slots[parent_pid.0].compare_exchange(
                        parent_head,
                        idx_delta,
                        std::sync::atomic::Ordering::AcqRel,
                        std::sync::atomic::Ordering::Relaxed,
                        &guard,
                    ) {
                        Ok(_) => {
                            break;
                        }
                        Err(CompareExchangeError { new, current }) => {
                            parent_head = current;

                            if has_index_entry(parent_head, &separator, &guard) {
                                // Someone else already added the index entry.
                                //
                                // Other threads help out when they see a SplitChild delta without
                                // a corresponding IndexEntry delta.
                                break;
                            }

                            // Avoid cloning the delta on every iteration
                            idx_delta = new;

                            // Update the next pointer to point to the current head.
                            // This is necessary so that we can avoid reallocating the delta entry.
                            match idx_delta.as_mut() {
                                Page::Delta(delta_entry) => {
                                    delta_entry
                                        .next
                                        .store(parent_head, std::sync::atomic::Ordering::Release);
                                }
                                _ => unreachable!(),
                            }
                        }
                    }
                }
            }
            Page::BaseIndex(_items) => {
                todo!("Split base index");
            }
            _ => {
                panic!("Encountered an unexpected delta page. Split should only be called directly after consolidation.");
            }
        }

        self.slots
            .push(Atomic::new(Page::BaseLeaf(ArcSlice::empty())));

        Ok(())
    }

    fn load<'a>(&self, index: PID, guard: &'a crossbeam::epoch::Guard) -> Shared<'a, Page<K, V>> {
        self.slots[index.0].load(std::sync::atomic::Ordering::Acquire, &guard)
    }

    fn find_leaf(
        &self,
        mut pid: PID,
        key: &K,
        stack: &mut Vec<PID>,
        guard: &crossbeam::epoch::Guard,
    ) -> PID {
        loop {
            stack.push(pid);
            let mut head = self.load(pid, guard);
            // write!(std::io::stdout(), "head: {:?}", head).unwrap();

            'inner: loop {
                // Safety: We are guaranteed that the pointer is non-null because we
                // always initialize slots before pointing at them. The allocation is guaranteed
                // to be valid because we are holding a guard and the output's lifetime is bound
                // to that of the guard.
                let page = unsafe { &*head.as_raw() };

                match page {
                    Page::Delta(DeltaEntry {
                        delta: Delta::SplitChild { separator, right },
                        ..
                    }) if key >= separator => {
                        pid = *right;
                        head = self.load(pid, guard);
                        continue 'inner;
                    }
                    Page::Delta(delta) => {
                        head = delta.next.load(std::sync::atomic::Ordering::Acquire, guard);
                    }
                    Page::BaseIndex(items) => {
                        pid = match items.binary_search_by_key(&key, |(k, _)| k) {
                            Ok(i) | Err(i) => items[i].1,
                        };
                        break 'inner;
                    }
                    Page::BaseLeaf(_) => {
                        return pid;
                    }
                }
            }
        }
    }

    fn find_in_slot<'a>(
        &self,
        pid: PID,
        key: &K,
        guard: &'a crossbeam::epoch::Guard,
    ) -> Option<(&'a K, &'a V)> {
        let mut ptr = self.load(pid, &guard);

        loop {
            // Safety: We are guaranteed that the pointer is non-null because we
            // always initialize slots before pointing at them. The allocation is guaranteed
            // to be valid because we are holding a guard and the output's lifetime is bound
            // to that of the guard.
            let page = unsafe { &*ptr.as_raw() };

            match page {
                Page::Delta(DeltaEntry { delta, next }) => match delta {
                    Delta::Insert {
                        key: rec_key,
                        value,
                    } if rec_key == key => {
                        return Some((rec_key, value));
                    }
                    Delta::Delete { key: rec_key } if rec_key == key => return None,
                    Delta::SplitChild { separator, right } => {
                        if key >= separator {
                            return self.find_in_slot(*right, key, guard);
                        } else {
                            ptr = next.load(std::sync::atomic::Ordering::Acquire, &guard);
                        }
                    }
                    // Delta::MergeSibling { separator, right } => todo!(),
                    _ => {
                        ptr = next.load(std::sync::atomic::Ordering::Acquire, &guard);
                    }
                },
                Page::BaseIndex(items) => match items.binary_search_by_key(&key, |(k, _)| k) {
                    Ok(index) => {
                        let (_k, pid) = &items[index];
                        ptr = self.load(*pid, guard);
                        continue;
                    }
                    Err(_) => {}
                },
                Page::BaseLeaf(items) => {
                    return items
                        .binary_search_by_key(&key, |(k, _)| k)
                        .ok()
                        .map(|index| (&items[index].0, &items[index].1));
                }
            }
        }
    }
}

#[test]
fn basic_test() {
    let table = BwTreeMap::<usize, usize>::new();

    assert_eq!(table.get(&1).map(|x| *x), None);

    table.insert(1, 2);
    assert_eq!(table.get(&1).map(|x| *x), Some(&2));

    table.insert(1, 3);
    assert_eq!(table.get(&1).map(|x| *x), Some(&3));

    table.insert(2, 3);
    assert_eq!(table.get(&2).map(|x| *x), Some(&3));
}

#[test]
fn insert_and_get_multiple_values() {
    let tree = BwTreeMap::<i32, String>::new();

    tree.insert(10, "ten".to_string());
    tree.insert(20, "twenty".to_string());
    tree.insert(30, "thirty".to_string());

    assert_eq!(
        tree.get(&10).map(|r| r.value().clone()),
        Some("ten".to_string())
    );
    assert_eq!(
        tree.get(&20).map(|r| r.value().clone()),
        Some("twenty".to_string())
    );
    assert_eq!(
        tree.get(&30).map(|r| r.value().clone()),
        Some("thirty".to_string())
    );
    assert_eq!(tree.get(&40).map(|r| r.value()), None);
}

#[test]
fn update_existing_values() {
    let tree = BwTreeMap::<&str, i32>::new();

    tree.insert("a", 1);
    tree.insert("b", 2);
    tree.insert("c", 3);

    assert_eq!(tree.get(&"a").map(|r| *r.value()), Some(1));

    tree.insert("a", 10);
    tree.insert("b", 20);

    assert_eq!(tree.get(&"a").map(|r| *r.value()), Some(10));
    assert_eq!(tree.get(&"b").map(|r| *r.value()), Some(20));
    assert_eq!(tree.get(&"c").map(|r| *r.value()), Some(3));
}

#[test]
fn delete_values() {
    let tree = BwTreeMap::<i32, &str>::new();

    tree.insert(1, "one");
    tree.insert(2, "two");
    tree.insert(3, "three");

    assert_eq!(tree.get(&1).map(|r| *r.value()), Some("one"));
    assert_eq!(tree.get(&2).map(|r| *r.value()), Some("two"));

    tree.delete(1);
    assert_eq!(tree.get(&1).map(|r| r.value()), None);
    assert_eq!(tree.get(&2).map(|r| *r.value()), Some("two"));

    tree.delete(3);
    assert_eq!(tree.get(&3).map(|r| r.value()), None);

    tree.delete(2);
    assert_eq!(tree.get(&2).map(|r| r.value()), None);
}

#[test]
fn insert_after_delete() {
    let tree = BwTreeMap::<usize, usize>::new();

    tree.insert(42, 100);
    assert_eq!(tree.get(&42).map(|r| *r.value()), Some(100));

    tree.delete(42);
    assert_eq!(tree.get(&42).map(|r| r.value()), None);

    tree.insert(42, 200);
    assert_eq!(tree.get(&42).map(|r| *r.value()), Some(200));
}

#[test]
fn delete_nonexistent() {
    let tree = BwTreeMap::<i32, i32>::new();

    tree.insert(1, 10);
    tree.insert(2, 20);

    tree.delete(3); // Should not panic or cause issues

    assert_eq!(tree.get(&1).map(|r| *r.value()), Some(10));
    assert_eq!(tree.get(&2).map(|r| *r.value()), Some(20));
}

#[test]
fn ref_key_value_accessors() {
    let tree = BwTreeMap::<String, Vec<i32>>::new();

    let key = "test".to_string();
    let value = vec![1, 2, 3];

    tree.insert(key.clone(), value.clone());

    let reference = tree.get(&key).unwrap();

    assert_eq!(reference.key(), &key);
    assert_eq!(reference.value(), &value);
    assert_eq!(**reference, value);
}

#[test]
fn works_with_complex_types() {
    #[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
    struct TestKey {
        id: i32,
        name: String,
    }

    let tree = BwTreeMap::<TestKey, Vec<String>>::new();

    let key1 = TestKey {
        id: 1,
        name: "first".to_string(),
    };
    let key2 = TestKey {
        id: 2,
        name: "second".to_string(),
    };

    let value1 = vec!["a".to_string(), "b".to_string()];
    let value2 = vec!["c".to_string(), "d".to_string()];

    tree.insert(key1.clone(), value1.clone());
    tree.insert(key2.clone(), value2.clone());

    assert_eq!(tree.get(&key1).map(|r| r.value().clone()), Some(value1));
    assert_eq!(tree.get(&key2).map(|r| r.value().clone()), Some(value2));
}
