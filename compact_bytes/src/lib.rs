//! "Small string optimization" for a bytes.

use std::alloc;
use std::ptr::NonNull;

mod growable;
pub use growable::CompactBytes;

const INLINE_MASK: u8 = 0b1000_0000;

/// Fixed capacity inline buffer of bytes.
#[repr(C, align(8))]
#[derive(Copy, Clone)]
struct InlineBytes<const CAPACITY: usize> {
    buffer: [u8; CAPACITY],
    data: u8,
}

/// Inline storage for [`CompactBytes`].
type InlineBytes23 = InlineBytes<23>;
static_assertions::assert_eq_size!(InlineBytes23, Vec<u8>);

impl<const CAPACITY: usize> InlineBytes<CAPACITY> {
    /// The amount of bytes this [`InlineBytes`] can store inline.
    const CAPACITY: usize = CAPACITY;

    /// Create an [`InlineBytes`] from the provided slice.
    ///
    /// Safety:
    ///
    /// * `slice` must have a length less than or equal to `CAPACITY`.
    ///
    #[inline]
    pub unsafe fn new(slice: &[u8]) -> Self {
        debug_assert!(slice.len() <= CAPACITY);

        let len = slice.len();
        let mut buffer = [0u8; CAPACITY];

        // SAFETY: We know src and dst are valid for len bytes, nor do they overlap.
        unsafe {
            buffer
                .as_mut_ptr()
                .copy_from_nonoverlapping(slice.as_ptr(), len)
        };

        let data = INLINE_MASK | (len as u8);

        InlineBytes { buffer, data }
    }

    #[inline]
    pub const fn empty() -> Self {
        let buffer = [0u8; CAPACITY];

        // Even though the below statement as no effect, we leave it for better understanding.
        #[allow(clippy::identity_op)]
        let data = INLINE_MASK | 0;

        InlineBytes { buffer, data }
    }

    pub fn len(&self) -> usize {
        (self.data & !INLINE_MASK) as usize
    }

    /// Forces the length of [`InlineBytes`] to `new_len`.
    ///
    /// # Safety
    /// * `new_len` must be less than or equal to the generic `CAPACITY`.
    /// * `new_len` must be less than or equal to capacity.
    /// * The bytes at `old_len..new_len` must be initialized.
    ///
    unsafe fn set_len(&mut self, new_len: usize) {
        debug_assert!(new_len <= CAPACITY);
        self.data = INLINE_MASK | (new_len as u8);
    }
}

/// A growable heap allocation of bytes.
#[repr(C)]
struct HeapBytesGrowable {
    ptr: NonNull<u8>,
    len: usize,
    cap: usize,
}
static_assertions::assert_eq_size!(HeapBytesGrowable, Vec<u8>);

impl HeapBytesGrowable {
    /// The minimum allocation size for a [`HeapBytesGrowable`].
    pub const MIN_ALLOCATION_SIZE: usize = std::mem::size_of::<usize>() * 2;
    /// The maximum allocation size for a [`HeapBytesGrowable`].
    pub const MAX_ALLOCATION_SIZE: usize = usize::MAX >> 1;

    #[inline]
    pub fn new(slice: &[u8]) -> Self {
        let len = slice.len();
        let cap = len.max(Self::MIN_ALLOCATION_SIZE);

        debug_assert!(cap <= Self::MAX_ALLOCATION_SIZE, "too large of allocation");
        let ptr = heap::alloc_ptr(cap);

        unsafe { ptr.as_ptr().copy_from_nonoverlapping(slice.as_ptr(), len) };

        HeapBytesGrowable { ptr, len, cap }
    }

    pub fn with_capacity(capacity: usize) -> Self {
        assert!(
            capacity <= Self::MAX_ALLOCATION_SIZE,
            "too large of allocation"
        );

        let len = 0;
        let cap = capacity.max(Self::MIN_ALLOCATION_SIZE);
        let ptr = heap::alloc_ptr(cap);

        HeapBytesGrowable {
            ptr,
            len,
            cap: capacity,
        }
    }

    pub fn with_additional(slice: &[u8], additional: usize) -> Self {
        let new_capacity = Self::amortized_growth(slice.len(), additional);
        let mut row = Self::with_capacity(new_capacity);

        debug_assert!(row.cap > slice.len());

        // SAFETY: We know src and dst are both valid for len bytes, nor are they overlapping.
        unsafe {
            std::ptr::copy_nonoverlapping(slice.as_ptr(), row.ptr.as_ptr(), slice.len());
        };
        // Set our length.
        row.len = slice.len();

        row
    }

    pub unsafe fn set_len(&mut self, len: usize) {
        self.len = len;
    }

    pub fn realloc(&mut self, new_capacity: usize) -> Result<usize, ()> {
        // Can't shrink the heap allocation to be less than length, because we'd lose data.
        if new_capacity < self.len {
            return Err(());
        }
        // Do not reallocate to 0 capacity.
        if new_capacity == 0 {
            return Err(());
        }

        // Always allocate some minimum amount of bytes.
        let new_capacity = new_capacity.max(Self::MIN_ALLOCATION_SIZE);

        // Already at the appropriate size!
        if new_capacity == self.cap {
            return Ok(new_capacity);
        }

        let cur_layout = heap::layout(self.cap);
        let new_layout = heap::layout(new_capacity);

        // Check for overflow.
        let new_size = new_layout.size();
        if new_size < new_capacity {
            return Err(());
        }

        // SAFETY:
        // * Our pointer was allocated via the same allocator.
        // * We used the same layout for the previous allocation.
        // * `new_size` is correct.
        let raw_ptr = unsafe { alloc::realloc(self.ptr.as_ptr(), cur_layout, new_size) };
        let ptr = NonNull::new(raw_ptr).ok_or(())?;

        self.ptr = ptr;
        self.cap = new_capacity;

        Ok(new_capacity)
    }

    #[inline]
    fn dealloc(&mut self) {
        heap::dealloc_ptr(self.ptr, self.cap);
    }

    /// [`HeapBytes`] grows at an amortized rates of 1.5x
    ///
    /// Note: this is different than [`std::vec::Vec`], which grows at a rate of 2x. It's debated
    /// which is better, for now we'll stick with a rate of 1.5x
    #[inline(always)]
    pub fn amortized_growth(cur_len: usize, additional: usize) -> usize {
        let required = cur_len.saturating_add(additional);
        let amortized = cur_len.saturating_mul(3) / 2;
        amortized.max(required)
    }
}

impl Drop for HeapBytesGrowable {
    fn drop(&mut self) {
        self.dealloc()
    }
}


    #[inline]

mod heap {
    use std::alloc;
    use std::ptr::NonNull;

    /// Create an allocation with [`layout`].
    #[inline]
    pub(crate) fn alloc_ptr(capacity: usize) -> NonNull<u8> {
        let layout = layout(capacity);
        debug_assert!(layout.size() > 0);

        // SAFETY: We ensure that the layout is not zero sized, by enforcing a minimum size.
        let ptr = unsafe { alloc::alloc(layout) };

        NonNull::new(ptr).expect("failed to allocate HeapRow")
    }

    /// Drop an allocation that was created with [`layout`].
    #[inline]
    pub(crate) fn dealloc_ptr(ptr: NonNull<u8>, capacity: usize) {
        let layout = layout(capacity);

        // SAFETY:
        // * The pointer was allocated via this allocator.
        // * We used the same layout when allocating.
        unsafe { alloc::dealloc(ptr.as_ptr(), layout) };
    }

    /// Returns the [`alloc::Layout`] for [`HeapBytesGrowable`] and [`HeapBytesSlice`].
    ///
    /// [`HeapBytesGrowable`]: super::HeapBytesGrowable
    /// [`HeapBytesSlice`]: super::HeapBytesSlice
    #[inline(always)]
    pub(crate) fn layout(capacity: usize) -> alloc::Layout {
        debug_assert!(capacity > 0, "tried to allocate a HeapRow with 0 capacity");
        alloc::Layout::array::<u8>(capacity).expect("valid capacity")
    }
}
