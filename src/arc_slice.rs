use std::{
    ops::{Bound, Deref, Index, Range, RangeBounds},
    sync::Arc,
};

/// Immutable, shareable subslice with O(1) slicing.
///
/// Cloning is cheap; dropping decrements the shared reference count.
#[derive(Clone)]
pub struct ArcSlice<T> {
    data: Arc<[T]>,
    start: usize,
    len: usize,
}

impl<T> ArcSlice<T> {
    pub fn new(data: Arc<[T]>) -> Self {
        Self {
            start: 0,
            len: data.len(),
            data,
        }
    }

    pub fn empty() -> Self {
        Self {
            data: Arc::new([]),
            start: 0,
            len: 0,
        }
    }

    /// Wrap an owned vector (no copy).
    pub fn from_vec(v: Vec<T>) -> Self {
        let len = v.len();
        Self {
            data: Arc::<[T]>::from(v),
            start: 0,
            len,
        }
    }

    /// Wrap an existing `Arc<[T]>` (useful when you already have shared data).
    pub fn from_arc(data: Arc<[T]>) -> Self {
        let len = data.len();
        Self {
            data,
            start: 0,
            len,
        }
    }

    /// The subslice as a plain `&[T]`.
    #[inline]
    pub fn as_slice(&self) -> &[T] {
        &self.data[self.start..self.start + self.len]
    }

    /// Total number of elements in *this* view (not the full allocation!).
    #[inline]
    pub fn len(&self) -> usize {
        self.len
    }

    /// `true` if the view is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Create a further subslice in **O(1)**.
    ///
    /// Panics if the range is out‑of‑bounds for this view.
    pub fn slice<R>(&self, range: R) -> Self
    where
        R: RangeBounds<usize>,
    {
        // Convert the requested range into absolute indices relative to self.
        let Range { start, end } = normalize(range, self.len);

        Self {
            data: self.data.clone(),
            start: self.start + start,
            len: end - start,
        }
    }
}

/// Normalise an arbitrary `RangeBounds` into `Range { start, end }`,
/// checking bounds against `parent_len`.
fn normalize<R>(range: R, parent_len: usize) -> Range<usize>
where
    R: RangeBounds<usize>,
{
    let start = match range.start_bound() {
        Bound::Included(&i) => i,
        Bound::Excluded(&i) => i + 1,
        Bound::Unbounded => 0,
    };
    let end = match range.end_bound() {
        Bound::Included(&i) => i + 1,
        Bound::Excluded(&i) => i,
        Bound::Unbounded => parent_len,
    };

    assert!(
        start <= end && end <= parent_len,
        "slice index out of bounds"
    );
    Range { start, end }
}

impl<T> Deref for ArcSlice<T> {
    type Target = [T];
    fn deref(&self) -> &Self::Target {
        self.as_slice()
    }
}

impl<T> AsRef<[T]> for ArcSlice<T> {
    fn as_ref(&self) -> &[T] {
        self.as_slice()
    }
}

impl<T, I> Index<I> for ArcSlice<T>
where
    I: std::slice::SliceIndex<[T]>,
{
    type Output = I::Output;

    fn index(&self, index: I) -> &Self::Output {
        Index::index(self.as_slice(), index)
    }
}

impl<T: std::fmt::Debug> std::fmt::Debug for ArcSlice<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("RcSlice").field(&self.as_slice()).finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic_subslicing() {
        let data = ArcSlice::from_vec(vec![0, 1, 2, 3, 4, 5]);

        // Make two overlapping sub‑views.
        let left = data.slice(..3); // [0,1,2]
        let right = data.slice(2..); // [2,3,4,5]

        assert_eq!(&*left, &[0, 1, 2]);
        assert_eq!(&*right, &[2, 3, 4, 5]);

        // Further slice without copying.
        let middle = right.slice(1..3); // [3,4]
        assert_eq!(&*middle, &[3, 4]);

        // Confirm they all share one allocation.
        assert_eq!(Arc::strong_count(&data.data), 4);
    }
}
