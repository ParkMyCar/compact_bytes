use std::fmt;
use std::hash::{Hash, Hasher};
use std::mem::ManuallyDrop;
use std::ops::Deref;
use std::ops::DerefMut;
use std::ptr::NonNull;

use crate::{HeapBytesFixed, InlineBytes15, INLINE_MASK};

/// [`CompactBytesSlice`] inlines up-to 15 bytes on the stack, if more than that is required we
/// spill to the heap. The heap representation is not reference counted like `bytes::Bytes`.
///
/// Whereas a [`CompactBytes`] is like a `Vec<u8>`, [`CompactBytesSlice`] is like a `Box<[u8]>`.
pub union CompactBytesSlice {
    heap: ManuallyDrop<HeapBytesFixed>,
    inline: InlineBytes15,
}

static_assertions::assert_eq_align!(
    InlineBytes15,
    HeapBytesFixed,
    CompactBytesSlice,
    Box<[u8]>,
    usize
);
static_assertions::assert_eq_size!(InlineBytes15, HeapBytesFixed, CompactBytesSlice, Box<[u8]>);
static_assertions::const_assert_eq!(std::mem::size_of::<CompactBytesSlice>(), 16);

// SAFETY: It is safe to Send a `CompactBytesSlice` to other threads because it
// owns all of its data.
unsafe impl Send for CompactBytesSlice {}

// SAFETY: It is safe to share references of `CompactBytesSlice` between
// threads because it does not support any kind of interior mutability, or
// other way to introduce races.
unsafe impl Sync for CompactBytesSlice {}

impl CompactBytesSlice {
    /// The maximum amount of bytes that a [`CompactBytesSlice`] can store inline.
    pub const MAX_INLINE: usize = InlineBytes15::CAPACITY;

    // Note: Unlike `CompactBytes` we do not have a minimum heap allocation size
    // because our heap allocations are always exactly `len` bytes.

    /// The maximum amount of bytes that a [`CompactBytesSlice`] can store on the heap.
    pub const MAX_HEAP: usize = usize::MAX >> 1;

    /// Creates a new [`CompactBytesSlice`] from the provided slice. Stores the
    /// bytes inline if small enough.
    ///
    /// # Examples
    ///
    /// ```
    /// use compact_bytes::CompactBytesSlice;
    ///
    /// let inline = CompactBytesSlice::new(&[1, 2, 3, 4]);
    /// assert!(!inline.spilled());
    /// assert_eq!(inline.len(), 4);
    ///
    /// let heap = CompactBytesSlice::new(b"I am a bytes type that will get stored on the heap");
    /// assert!(heap.spilled());
    /// assert_eq!(heap.len(), 50);
    /// ```
    #[inline]
    pub fn new(slice: &[u8]) -> Self {
        if slice.len() <= Self::MAX_INLINE {
            // SAFETY: We just checked that slice length is less than or equal to MAX_INLINE.
            let inline = unsafe { InlineBytes15::new(slice) };
            CompactBytesSlice { inline }
        } else {
            let heap = ManuallyDrop::new(HeapBytesFixed::new(slice));
            CompactBytesSlice { heap }
        }
    }

    /// Creates a new empty [`CompactBytesSlice`] a capacity of
    /// [`CompactBytesSlice::MAX_INLINE`]. The function can be called in
    /// `const` contexts.
    ///
    /// # Examples
    ///
    /// ```
    /// use compact_bytes::CompactBytesSlice;
    ///
    /// let min = CompactBytesSlice::empty();
    /// assert_eq!(min.capacity(), CompactBytesSlice::MAX_INLINE);
    /// ```
    #[inline]
    pub const fn empty() -> Self {
        let inline = InlineBytes15::empty();
        CompactBytesSlice { inline }
    }

    /// Creates a new [`CompactBytesSlice`] using the provided pointer and length.
    ///
    /// # Safety
    ///
    /// * The caller must guarantee that the provided pointer is properly aligned, and the backing
    ///   allocation was made by the same allocator that will eventually be used to free the
    ///   returned [`CompactBytesSlice`].
    /// * `length` needs to be the capacity that the pointer was allocated with.
    /// * `length` needs to be less than or equal to [`CompactBytesSlice::MAX_HEAP`].
    ///
    #[inline]
    pub unsafe fn from_raw_parts(ptr: *mut u8, length: usize) -> Self {
        let heap = HeapBytesFixed {
            ptr: NonNull::new_unchecked(ptr),
            len: length,
        };
        let heap = ManuallyDrop::new(heap);
        CompactBytesSlice { heap }
    }

    /// Returns the contents of the [`CompactBytesSlice`] as a bytes slice.
    #[inline]
    pub fn as_slice(&self) -> &[u8] {
        let pointer = self.as_ptr();
        let length = self.len();

        unsafe { core::slice::from_raw_parts(pointer, length) }
    }

    /// Returns the contents of the [`CompactBytesSlice`] as a mutable bytes slice.
    #[inline]
    pub fn as_mut_slice(&mut self) -> &mut [u8] {
        let pointer = self.as_mut_ptr();
        let length = self.len();

        unsafe { core::slice::from_raw_parts_mut(pointer, length) }
    }

    /// Returns the length of the [`CompactBytesSlice`].
    #[inline(always)]
    pub fn len(&self) -> usize {
        // SAFETY: `InlineBytes15` and `HeapBytesFixed` have the same size and alignment.
        //
        // Note: This code is very carefully written so we can benefit from branchless
        // instructions.
        //
        // Note: If the `CompactBytesSlice`
        let (mut length, heap_length) = unsafe { (self.inline.len(), self.heap.len) };
        if self.spilled() {
            length = heap_length;
        }

        length
    }

    /// Returns if the [`CompactBytesSlice`] is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns the capacity of the [`CompactBytesSlice`].
    #[inline(always)]
    pub fn capacity(&self) -> usize {
        // SAFETY: `InlineBytes15` and `HeapBytesFixed` share the same size and alignment.
        //
        // Note: This code is very carefully written so we can benefit from branchless
        // instructions.
        let (mut capacity, heap_capacity) = unsafe { (Self::MAX_INLINE, self.heap.len) };
        if self.spilled() {
            capacity = heap_capacity;
        }
        capacity
    }

    /// Consumes the [`CompactBytesSlice`], returning a `Box<[u8]>`.
    #[inline]
    pub fn into_boxed_slice(self) -> Box<[u8]> {
        if self.spilled() {
            // SAFETY: `InlineBytes15` and `HeapBytesFixed` have the same size and alignment.
            // Above we checked if the current `CompactBytesSlice` is heap allocated.
            let heap = unsafe { &self.heap };

            let slice = unsafe { core::slice::from_raw_parts_mut(heap.ptr.as_ptr(), heap.len) };
            let boxed = unsafe { Box::from_raw(slice) };
            std::mem::forget(self);

            boxed
        } else {
            // SAFETY: `InlineBytes15` and `HeapBytesFixed` have the same size and alignment.
            // Above we checked if the current `CompactBytesSlice` is heap allocated.
            let inline = unsafe { &self.inline };
            inline.buffer.into()
        }
    }

    /// Returns if the [`CompactBytesSlice`] has spilled to the heap.
    #[inline(always)]
    pub fn spilled(&self) -> bool {
        // We store whether or not a `CompactBytesSlice` has spilled to the
        // heap using the most significant bit of the last byte.
        //
        // SAFETY: `InlineBytes15` and `HeapBytesFixed` have the same size and alignment.
        unsafe { self.inline.data < INLINE_MASK }
    }

    #[inline(always)]
    fn as_ptr(&self) -> *const u8 {
        // SAFETY: `InlineBytes15` and `HeapBytesFixed` have the same size and alignment.
        //
        // Note: This code is very carefully written so we can benefit from branchless
        // instructions.
        let mut pointer = self as *const Self as *const u8;
        if self.spilled() {
            pointer = unsafe { self.heap.ptr }.as_ptr()
        }
        pointer
    }

    #[inline(always)]
    fn as_mut_ptr(&mut self) -> *mut u8 {
        // SAFETY: `InlineBytes15` and `HeapBytesFixed` have the same size and alignment.
        //
        // Note: This code is very carefully written so we can benefit from branchless
        // instructions.
        let mut pointer = self as *mut Self as *mut u8;
        if self.spilled() {
            pointer = unsafe { self.heap.ptr }.as_ptr()
        }
        pointer
    }
}

impl Default for CompactBytesSlice {
    #[inline]
    fn default() -> Self {
        CompactBytesSlice::new(&[])
    }
}

impl Deref for CompactBytesSlice {
    type Target = [u8];

    #[inline]
    fn deref(&self) -> &[u8] {
        self.as_slice()
    }
}

impl DerefMut for CompactBytesSlice {
    #[inline]
    fn deref_mut(&mut self) -> &mut [u8] {
        self.as_mut_slice()
    }
}

impl AsRef<[u8]> for CompactBytesSlice {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.as_slice()
    }
}

impl<T: AsRef<[u8]>> PartialEq<T> for CompactBytesSlice {
    #[inline]
    fn eq(&self, other: &T) -> bool {
        self.as_slice() == other.as_ref()
    }
}

impl Eq for CompactBytesSlice {}

impl Hash for CompactBytesSlice {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.as_slice().hash(state)
    }
}

impl fmt::Debug for CompactBytesSlice {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.as_slice())
    }
}

impl Drop for CompactBytesSlice {
    #[inline]
    fn drop(&mut self) {
        // Note: we hint to the compiler that dropping a heap variant is cold to improve the
        // performance of dropping the inline variant.
        #[cold]
        fn outlined_drop(this: &mut CompactBytesSlice) {
            let heap = unsafe { &mut this.heap };
            heap.dealloc();
        }

        if self.spilled() {
            outlined_drop(self);
        }
    }
}

impl Clone for CompactBytesSlice {
    #[inline]
    fn clone(&self) -> Self {
        // Note: we hint to the compiler that cloning a heap variant is cold to improve the
        // performance of cloning the inline variant.
        #[cold]
        fn outlined_clone(this: &CompactBytesSlice) -> CompactBytesSlice {
            CompactBytesSlice::new(this.as_slice())
        }

        if self.spilled() {
            outlined_clone(self)
        } else {
            let inline = unsafe { &self.inline };
            CompactBytesSlice { inline: *inline }
        }
    }
}

impl From<Box<[u8]>> for CompactBytesSlice {
    #[inline]
    fn from(value: Box<[u8]>) -> Self {
        if value.is_empty() {
            return CompactBytesSlice::empty();
        }

        // "leak" the Box so dropping the value does not de-allocate the backing buffer.
        let slice = Box::leak(value);
        // Use the returned pointer and length to construct a CompactBytesSlice in constant time.
        let (ptr, len) = (slice.as_mut_ptr(), slice.len());
        // SAFETY: We checked above, and returned early, if the `Box` was empty, thus we know this
        // pointer is not null.
        let ptr = unsafe { NonNull::new_unchecked(ptr) };

        let heap = HeapBytesFixed { ptr, len };
        CompactBytesSlice {
            heap: ManuallyDrop::new(heap),
        }
    }
}

#[cfg(test)]
mod test {
    use proptest::prelude::*;
    use test_case::test_case;
    use test_strategy::proptest;

    use super::{CompactBytesSlice, HeapBytesFixed};

    #[test]
    fn test_empty() {
        let obj = const { CompactBytesSlice::empty() };
        assert_eq!(obj.as_slice(), [0u8; 0].as_slice());
        assert!(obj.is_empty());
        assert!(!obj.spilled())
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_discriminant() {
        let mut buf = vec![0u8; 32];
        let heap = HeapBytesFixed {
            ptr: unsafe { std::ptr::NonNull::new_unchecked(buf.as_mut_ptr()) },
            len: usize::MAX >> 1,
        };
        let repr = CompactBytesSlice {
            heap: std::mem::ManuallyDrop::new(heap),
        };
        assert!(repr.spilled());
        // mem::forget the repr since it's underlying buffer is shared.
        std::mem::forget(repr);

        let bad_heap = HeapBytesFixed {
            ptr: unsafe { std::ptr::NonNull::new_unchecked(buf.as_mut_ptr()) },
            len: usize::MAX,
        };
        let repr = CompactBytesSlice {
            heap: std::mem::ManuallyDrop::new(bad_heap),
        };
        // This will identify as inline since the MSB is 1.
        assert!(!repr.spilled());
        // mem::forget the repr since it's underlying buffer is shared.
        std::mem::forget(repr);
    }

    #[test_case(&[], 0 ; "empty")]
    #[test_case(b"hello world", 11 ; "short")]
    #[test_case(b"15 bytes inline", 15 ; "max_inline")]
    #[test_case(b"16 bytes spills!", 16 ; "first_spill")]
    #[test_case(b"i am very large and will spill to the heap", 42 ; "heap")]
    fn smoketest_row(slice: &[u8], expected_len: usize) {
        let repr = CompactBytesSlice::new(slice);

        assert_eq!(repr.len(), expected_len);
        assert_eq!(repr.as_slice(), slice);
        assert_eq!(repr.spilled(), expected_len > CompactBytesSlice::MAX_INLINE);
    }

    #[test_case(&[] ; "empty")]
    #[test_case(b"smol" ; "inline")]
    #[test_case(b"large large large large large large" ; "heap")]
    fn smoketest_clone(initial: &[u8]) {
        let repr_a = CompactBytesSlice::new(initial);
        let repr_b = repr_a.clone();

        assert_eq!(repr_a.len(), repr_b.len());
        assert_eq!(repr_a.capacity(), repr_b.capacity());
        assert_eq!(repr_a.as_slice(), repr_b.as_slice());
    }

    #[test_case(Box::from([]) ; "empty")]
    #[test_case(Box::from([0, 1, 2, 3, 4]) ; "inline")]
    #[test_case(b"I am long and will be on the heap, yada yada yada".to_vec().into_boxed_slice() ; "heap")]
    fn smoketest_from_box_slice(initial: Box<[u8]>) {
        let control = initial.clone();
        let pointer = initial.as_ptr();
        let repr = CompactBytesSlice::from(initial);

        assert_eq!(control.len(), repr.len());
        assert_eq!(&control[..], &repr[..]);

        // We do not eagerly inline, except if the Vec is empty.
        assert_eq!(repr.spilled(), !control.is_empty());
        // The allocation of the Vec should get re-used.
        assert_eq!(repr.as_ptr() == pointer, !control.is_empty());
    }

    #[test]
    fn test_cloning_inlines() {
        let data = Box::from([42u8]);
        let c = CompactBytesSlice::from(data);

        assert_eq!(c.as_slice(), &[42]);
        assert_eq!(c.capacity(), 1);
        assert!(c.spilled());

        let clone = c.clone();
        assert_eq!(clone.as_slice(), &[42]);
        assert_eq!(clone.capacity(), CompactBytesSlice::MAX_INLINE);
        assert!(!clone.spilled());
    }

    #[proptest]
    #[cfg_attr(miri, ignore)]
    fn proptest_row(initial: Vec<u8>) {
        let repr = CompactBytesSlice::new(&initial);

        prop_assert_eq!(repr.as_slice(), initial.as_slice());
        prop_assert_eq!(repr.len(), initial.len());
    }

    #[proptest]
    #[cfg_attr(miri, ignore)]
    fn proptest_clone(initial: Vec<u8>) {
        let repr_a = CompactBytesSlice::new(&initial);
        let repr_b = repr_a.clone();

        assert_eq!(repr_a.len(), repr_b.len());
        assert_eq!(repr_a.capacity(), repr_b.capacity());
        assert_eq!(repr_a.as_slice(), repr_b.as_slice());
    }

    #[proptest]
    #[cfg_attr(miri, ignore)]
    fn proptest_from_box_slice(initial: Box<[u8]>) {
        let control = initial.clone();
        let pointer = initial.as_ptr();
        let repr = CompactBytesSlice::from(initial);

        assert_eq!(control.len(), repr.len());
        assert_eq!(&control[..], &repr[..]);

        // We do not eagerly inline, except if the Vec is empty.
        assert_eq!(repr.spilled(), !control.is_empty());
        // The allocation of the Vec should get re-used.
        assert_eq!(repr.as_ptr() == pointer, !control.is_empty());
    }
}
