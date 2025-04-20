use crossbeam::epoch::{Atomic, CompareExchangeError, Guard, Owned, Shared};

#[derive(Debug, Clone, Copy)]
pub struct PID(usize);

#[repr(C)]
pub enum Delta<K, V> {
    Insert { key: K, value: V },
    Delete { key: K },

    SplitChild { separator: K, right: PID },
    // MergeSibling { separator: K, right: PID },
}

#[repr(C)]
pub struct DeltaEntry<K, V> {
    delta: Delta<K, V>,
    next: Atomic<Page<K, V>>,
}

#[repr(C)]
pub enum Page<K, V> {
    BaseLeaf(Box<[(K, V)]>),
    Delta(DeltaEntry<K, V>),
}

const ROOT_PID: PID = PID(0);

pub struct BwTreeMap<K, V> {
    slots: boxcar::Vec<Atomic<Page<K, V>>>,
}

impl<K: Ord + PartialEq + Clone + 'static, V> BwTreeMap<K, V> {
    pub fn new() -> Self {
        let slots = boxcar::Vec::with_capacity(4);

        for _ in 0..4 {
            slots.push(Atomic::null());
        }

        slots[ROOT_PID.0].store(
            Owned::new(Page::BaseLeaf(Box::new([]))),
            std::sync::atomic::Ordering::Relaxed,
        );

        Self { slots }
    }

    fn load<'a>(&self, index: PID, guard: &'a crossbeam::epoch::Guard) -> Shared<'a, Page<K, V>> {
        self.slots[index.0].load(std::sync::atomic::Ordering::Acquire, &guard)
    }

    fn find_leaf(&self, mut pid: PID, key: &K, guard: &Guard) -> PID {
        loop {
            let mut head = self.load(pid, guard);

            loop {
                // Safety: We are guaranteed that the pointer is non-null because we
                // always initialize slots before pointing at them. The allocation is guaranteed
                // to be valid because we are holding a guard and the output's lifetime is bound
                // to that of the guard.
                let page = unsafe { head.as_ref() }.expect("non-null");

                match page {
                    Page::BaseLeaf(_) => {
                        return pid;
                    }
                    Page::Delta(DeltaEntry { delta, next }) => match delta {
                        Delta::SplitChild { separator, right } if key >= separator => {
                            pid = *right;
                            head = self.load(pid, guard);
                            continue;
                        }
                        _ => {
                            head = next.load(std::sync::atomic::Ordering::Acquire, guard);
                        }
                    },
                }
            }
        }
    }

    pub fn insert<'a>(
        &self,
        key: K,
        value: V,
        guard: &'a crossbeam::epoch::Guard,
    ) -> Result<(), ()> {
        let pid = self.find_leaf(ROOT_PID, &key, &guard);

        let mut delta = Owned::new(Page::Delta(DeltaEntry {
            delta: Delta::Insert {
                key: key.clone(),
                value,
            },
            // We should never actually read this null pointer
            next: Atomic::null(),
        }));

        loop {
            let head = self.load(pid, &guard);

            // Optimistically check if the key already exists
            if let Some(_) = self.find_in_slot(pid, &key, &guard) {
                // TODO: Handle updates
                return Err(());
            }

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
                    return Ok(());
                }
                Err(CompareExchangeError { new, .. }) => {
                    // Avoid cloning the delta on every iteration
                    delta = new;
                }
            }
        }
    }

    pub fn get<'a>(&self, key: &K, guard: &'a Guard) -> Option<&'a V> {
        self.find_in_slot(ROOT_PID, key, guard)
    }

    pub fn find_in_slot<'a>(&self, pid: PID, key: &K, guard: &'a Guard) -> Option<&'a V> {
        let mut ptr = self.load(pid, &guard);

        loop {
            // Safety: We are guaranteed that the pointer is non-null because we
            // always initialize slots before pointing at them. The allocation is guaranteed
            // to be valid because we are holding a guard and the output's lifetime is bound
            // to that of the guard.
            let page = unsafe { ptr.as_ref().expect("non-null") };

            match page {
                Page::Delta(DeltaEntry { delta, next }) => match delta {
                    Delta::Insert {
                        key: rec_key,
                        value,
                    } if rec_key == key => {
                        return Some(value);
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
                Page::BaseLeaf(items) => {
                    return items
                        .binary_search_by_key(key, |(k, _)| k.clone())
                        .ok()
                        .map(|index| &items[index].1);
                }
            }
        }
    }
}

#[test]
fn basic_test() {
    let table = BwTreeMap::<usize, usize>::new();

    let guard = crossbeam::epoch::pin();

    assert_eq!(table.get(&1, &guard), None);

    table.insert(1, 2, &guard).unwrap();
    assert_eq!(table.get(&1, &guard), Some(&2));

    table.insert(2, 3, &guard).unwrap();
    assert_eq!(table.get(&2, &guard), Some(&3));
}
