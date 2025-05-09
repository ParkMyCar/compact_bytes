//! "Small string optimization" for a bytes.

use std::alloc;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::mem::ManuallyDrop;
use std::ops::Deref;
use std::ops::DerefMut;
use std::ptr::NonNull;

const INLINE_MASK: u8 = 0b1000_0000;

/// [`CompactBytes`] inlines up-to 23 bytes on the stack, if more than that is required we spill to
/// the heap. The heap representation is not reference counted like `bytes::Bytes`, it's just an
/// owned blob of bytes.
///
/// # Why?
///
/// ### 1. Do we want to do this?
///
/// Performance. A `Vec<u8>` is already 24 bytes on the stack, and then another allocation on the
/// heap. If we can avoid the heap allocation altogether it saves memory and improves runtime
/// performance.
///
/// ### 2. Did we write our own implementation?
///
/// At the time of writing (October 2023), there isn't anything else in the Rust ecosystem that
/// provides what we need. There is `smallvec` (which we used to use) but it's not space efficient.
/// A `SmallVec<[u8; 24]>` required 32 bytes on the stack, so we were wasting 8 bytes! There are
/// other small vector crates (e.g. `arrayvec` or `tinyvec`) but they have their own limitations.
/// There are also a number of small string optimizations in the Rust ecosystem, but none of them
/// work for other various reasons.
///
/// # How does this work?
///
/// A [`CompactBytes`] is 24 bytes on the stack (same as `Vec<u8>`) but it has two modes:
///
/// 1. Heap   `[ ptr<8> | len<8> | cap<8> ]`
/// 2. Inline `[   buffer<23>   | len <1> ]`
///
/// We use the most significant bit of the last byte to indicate which mode we're in.
///
pub union CompactBytes {
    heap: ManuallyDrop<HeapBytes>,
    inline: InlineBytes,
}

// SAFETY: It is safe to Send a `CompactBytes` to other threads because it owns all of its data.
unsafe impl Send for CompactBytes {}

// SAFETY: It is safe to share references of `CompactBytes` between threads because it does not
// support any kind of interior mutability, or other way to introduce races.
unsafe impl Sync for CompactBytes {}

static_assertions::assert_eq_align!(InlineBytes, HeapBytes, CompactBytes, Vec<u8>, usize);
static_assertions::assert_eq_size!(InlineBytes, HeapBytes, CompactBytes, Vec<u8>);

static_assertions::const_assert_eq!(std::mem::size_of::<CompactBytes>(), 24);

impl CompactBytes {
    /// The maximum amount of bytes that a [`CompactBytes`] can store inline.
    pub const MAX_INLINE: usize = 23;

    /// The minimum amount of bytes that a [`CompactBytes`] will store on the heap.
    pub const MIN_HEAP: usize = std::mem::size_of::<usize>() * 2;
    /// The maximum amount of bytes that a [`CompactBytes`] can store on the heap.
    pub const MAX_HEAP: usize = usize::MAX >> 1;

    /// Creates a new [`CompactBytes`] from the provided slice. Stores the bytes inline if small
    /// enough.
    ///
    /// # Examples
    ///
    /// ```
    /// use compact_bytes::CompactBytes;
    ///
    /// let inline = CompactBytes::new(&[1, 2, 3, 4]);
    /// assert!(!inline.spilled());
    /// assert_eq!(inline.len(), 4);
    ///
    /// let heap = CompactBytes::new(b"I am a bytes type that will get stored on the heap");
    /// assert!(heap.spilled());
    /// assert_eq!(heap.len(), 50);
    /// ```
    #[inline]
    pub fn new(slice: &[u8]) -> Self {
        if slice.len() <= Self::MAX_INLINE {
            // SAFETY: We just checked that slice length is less than or equal to MAX_INLINE.
            let inline = unsafe { InlineBytes::new(slice) };
            CompactBytes { inline }
        } else {
            let heap = ManuallyDrop::new(HeapBytes::new(slice));
            CompactBytes { heap }
        }
    }

    /// Creates a new [`CompactBytes`] with the specified capacity, but with a minimum of
    /// [`CompactBytes::MAX_INLINE`].
    ///
    /// # Examples
    ///
    /// ```
    /// use compact_bytes::CompactBytes;
    ///
    /// let min = CompactBytes::with_capacity(4);
    /// assert_eq!(min.capacity(), CompactBytes::MAX_INLINE);
    /// ```
    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        if capacity <= Self::MAX_INLINE {
            let inline = InlineBytes::empty();
            CompactBytes { inline }
        } else {
            let heap = ManuallyDrop::new(HeapBytes::with_capacity(capacity));
            CompactBytes { heap }
        }
    }

    /// Creates a new empty [`CompactBytes`] a capacity of [`CompactBytes::MAX_INLINE`]. The
    /// function can be called in `const` contexts.
    ///
    /// # Examples
    ///
    /// ```
    /// use compact_bytes::CompactBytes;
    ///
    /// let min = CompactBytes::empty();
    /// assert_eq!(min.capacity(), CompactBytes::MAX_INLINE);
    /// ```
    #[inline]
    pub const fn empty() -> Self {
        let inline = InlineBytes::empty();
        CompactBytes { inline }
    }

    /// Creates a new [`CompactBytes`] using the provided pointer, length, and capacity.
    ///
    /// # Safety
    ///
    /// * The caller must guarantee that the provided pointer is properly aligned, and the backing
    ///   allocation was made by the same allocator that will eventually be used to free the
    ///   returned [`CompactBytes`].
    /// * `length` needs to be less than or equal to `capacity`.
    /// * `capacity` needs to be the capacity that the pointer was allocated with.
    /// * `capacity` needs to be less than or equal to [`CompactBytes::MAX_HEAP`].
    ///
    #[inline]
    pub unsafe fn from_raw_parts(ptr: *mut u8, length: usize, capacity: usize) -> Self {
        let heap = HeapBytes {
            ptr: NonNull::new_unchecked(ptr),
            len: length,
            cap: capacity,
        };
        let heap = ManuallyDrop::new(heap);
        CompactBytes { heap }
    }

    /// Returns the contents of the [`CompactBytes`] as a bytes slice.
    #[inline]
    pub fn as_slice(&self) -> &[u8] {
        let pointer = self.as_ptr();
        let length = self.len();

        unsafe { core::slice::from_raw_parts(pointer, length) }
    }

    /// Returns the contents of the [`CompactBytes`] as a mutable bytes slice.
    #[inline]
    pub fn as_mut_slice(&mut self) -> &mut [u8] {
        let pointer = self.as_mut_ptr();
        let length = self.len();

        unsafe { core::slice::from_raw_parts_mut(pointer, length) }
    }

    /// Returns the length of the [`CompactBytes`].
    #[inline(always)]
    pub fn len(&self) -> usize {
        // SAFETY: `InlineBytes` and `HeapBytes` share the same size and alignment. Before
        // returning this value we check whether it's valid or not.
        //
        // Note: This code is very carefully written so we can benefit from branchless
        // instructions.
        let (mut length, heap_length) = unsafe { (self.inline.len(), self.heap.len) };
        if self.spilled() {
            length = heap_length;
        }

        length
    }

    /// Returns if the [`CompactBytes`] is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns the capacity of the [`CompactBytes`].
    #[inline(always)]
    pub fn capacity(&self) -> usize {
        // SAFETY: `InlineBytes` and `HeapBytes` share the same size and alignment. Before
        // returning this value we check whether it's valid or not.
        //
        // Note: This code is very carefully written so we can benefit from branchless
        // instructions.
        let (mut capacity, heap_capacity) = unsafe { (Self::MAX_INLINE, self.heap.cap) };
        if self.spilled() {
            capacity = heap_capacity;
        }
        capacity
    }

    /// Appends an additional byte to the [`CompactBytes`], resizing if necessary.
    ///
    /// Note: You should almost never call this in a loop, instead use
    /// [`CompactBytes::extend_from_slice`].
    #[inline]
    pub fn push(&mut self, byte: u8) {
        self.extend_from_slice(&[byte]);
    }

    /// Extends the [`CompactBytes`] with bytes from `slice`, resizing if necessary.
    #[inline(always)]
    pub fn extend_from_slice(&mut self, slice: &[u8]) {
        // Reserve at least enough space to fit slice.
        self.reserve(slice.len());

        let (ptr, len, cap) = self.as_mut_triple();
        // SAFTEY: `len` is less than `cap`, so we know it's within the original allocation. This
        // addition does not overflow `isize`, nor does it rely on any wrapping logic.
        let push_ptr = unsafe { ptr.add(len) };

        debug_assert!((cap - len) >= slice.len(), "failed to reserve enough space");

        // Safety:
        //
        // * src is valid for a read of len bytes, since len comes from src.
        // * dst is valid for writes of len bytes, since we just reserved extra space.
        // * src and dst are both properly aligned.
        // * src and dst to not overlap because we have a unique reference to dst.
        //
        unsafe { std::ptr::copy_nonoverlapping(slice.as_ptr(), push_ptr, slice.len()) };

        // SAFETY: We just wrote an additional len bytes, so we know this length is valid.
        unsafe { self.set_len(len + slice.len()) };
    }

    /// Truncates this [`CompactBytes`], removing all contents but without effecting the capacity.
    #[inline]
    pub fn clear(&mut self) {
        self.truncate(0);
    }

    /// Truncates this [`CompactBytes`] to the specified length without effecting the capacity. Has
    /// no effect if `new_len` is greater than the current length.
    #[inline]
    pub fn truncate(&mut self, new_len: usize) {
        if new_len >= self.len() {
            return;
        }
        unsafe { self.set_len(new_len) }
    }

    /// Reserves at least `additional` bytes for this [`CompactBytes`], possibly re-allocating if
    /// there is not enough remaining capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use compact_bytes::CompactBytes;
    ///
    /// let mut b = CompactBytes::new(b"foo");
    /// b.reserve(100);
    ///
    /// assert_eq!(b.capacity(), 103);
    /// ```
    #[inline]
    pub fn reserve(&mut self, additional: usize) {
        let len = self.len();
        let needed_capacity = len
            .checked_add(additional)
            .expect("attempt to reserve more than usize::MAX");

        // Already have enough space, nothing to do!
        if self.capacity() >= needed_capacity {
            return;
        }

        // Note: We move the actual re-allocation code path into its own function
        // so the common case of calling `reserve(...)` when we already have
        // enough capacity can be inlined by LLVM.
        realloc(self, len, additional);

        #[cold]
        fn realloc(this: &mut CompactBytes, len: usize, additional: usize) {
            // Note: Here we are making a distinct choice to _not_ eagerly inline.
            //
            // `CompactBytes`s can get re-used, e.g. calling `CompactBytes::clear`, at which point it's
            // possible  we could have a length of 0, and 'additional' bytes would be less then
            // `MAX_INLINE`. Some implementations might opt to drop the existing heap allocation, but
            // if a `CompactBytes` is being re-used it's likely we'll need the full original capacity,
            // thus we do not eagerly inline.

            if !this.spilled() {
                let heap = HeapBytes::with_additional(this.as_slice(), additional);
                *this = CompactBytes {
                    heap: ManuallyDrop::new(heap),
                };
            } else {
                // SAFETY: `InlineBytes` and `HeapBytes` have the same size and alignment. We also
                // checked above that the current `CompactBytes` is heap allocated.
                let heap_row = unsafe { &mut this.heap };

                let amortized_capacity = HeapBytes::amortized_growth(len, additional);

                // First attempt to resize the existing allocation, if that fails then create a new one.
                if heap_row.realloc(amortized_capacity).is_err() {
                    let heap = HeapBytes::with_additional(this.as_slice(), additional);
                    let heap = ManuallyDrop::new(heap);
                    *this = CompactBytes { heap };
                }
            }
        }
    }

    /// Consumes the [`CompactBytes`], returning a `Vec<u8>`.
    #[inline]
    pub fn into_vec(self) -> Vec<u8> {
        if self.spilled() {
            // SAFETY: `InlineBytes` and `HeapBytes` have the same size and alignment. We also
            // checked above that the current `CompactBytes` is heap allocated.
            let heap = unsafe { &self.heap };
            let vec = unsafe { Vec::from_raw_parts(heap.ptr.as_ptr(), heap.len, heap.cap) };
            std::mem::forget(self);

            vec
        } else {
            self.as_slice().to_vec()
        }
    }

    /// Returns if the [`CompactBytes`] has spilled to the heap.
    #[inline(always)]
    pub fn spilled(&self) -> bool {
        // SAFETY: `InlineBytes` and `HeapBytes` have the same size and alignment. We also checked
        // above that the current `CompactBytes` is heap allocated.
        unsafe { self.inline.data < INLINE_MASK }
    }

    /// Forces the length of [`CompactBytes`] to `new_len`.
    ///
    /// # Safety
    /// * `new_len` must be less than or equal to capacity.
    /// * The bytes at `old_len..new_len` must be initialized.
    ///
    #[inline]
    unsafe fn set_len(&mut self, new_len: usize) {
        if self.spilled() {
            self.heap.set_len(new_len);
        } else {
            self.inline.set_len(new_len);
        }
    }

    #[inline(always)]
    fn as_ptr(&self) -> *const u8 {
        // SAFETY: `InlineBytes` and `HeapBytes` share the same size and alignment. Before
        // returning this value we check whether it's valid or not.
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
        // SAFETY: `InlineBytes` and `HeapBytes` share the same size and alignment. Before
        // returning this value we check whether it's valid or not.
        //
        // Note: This code is very carefully written so we can benefit from branchless
        // instructions.
        let mut pointer = self as *mut Self as *mut u8;
        if self.spilled() {
            pointer = unsafe { self.heap.ptr }.as_ptr()
        }
        pointer
    }

    #[inline(always)]
    fn as_mut_triple(&mut self) -> (*mut u8, usize, usize) {
        let ptr = self.as_mut_ptr();
        let len = self.len();
        let cap = self.capacity();

        (ptr, len, cap)
    }
}

impl Default for CompactBytes {
    #[inline]
    fn default() -> Self {
        CompactBytes::new(&[])
    }
}

impl Deref for CompactBytes {
    type Target = [u8];

    #[inline]
    fn deref(&self) -> &[u8] {
        self.as_slice()
    }
}

impl DerefMut for CompactBytes {
    #[inline]
    fn deref_mut(&mut self) -> &mut [u8] {
        self.as_mut_slice()
    }
}

impl AsRef<[u8]> for CompactBytes {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.as_slice()
    }
}

impl<T: AsRef<[u8]>> PartialEq<T> for CompactBytes {
    #[inline]
    fn eq(&self, other: &T) -> bool {
        self.as_slice() == other.as_ref()
    }
}

impl Eq for CompactBytes {}

impl Hash for CompactBytes {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.as_slice().hash(state)
    }
}

impl fmt::Debug for CompactBytes {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.as_slice())
    }
}

impl Drop for CompactBytes {
    #[inline]
    fn drop(&mut self) {
        // Note: we hint to the compiler that dropping a heap variant is cold to improve the
        // performance of dropping the inline variant.
        #[cold]
        fn outlined_drop(this: &mut CompactBytes) {
            let heap = unsafe { &mut this.heap };
            heap.dealloc();
        }

        if self.spilled() {
            outlined_drop(self);
        }
    }
}

impl Clone for CompactBytes {
    #[inline]
    fn clone(&self) -> Self {
        // Note: we hint to the compiler that cloing a heap variant is cold to improve the
        // performance of cloning the inline variant.
        #[cold]
        fn outlined_clone(this: &CompactBytes) -> CompactBytes {
            CompactBytes::new(this.as_slice())
        }

        if self.spilled() {
            outlined_clone(self)
        } else {
            let inline = unsafe { &self.inline };
            CompactBytes { inline: *inline }
        }
    }

    #[inline]
    fn clone_from(&mut self, source: &Self) {
        self.clear();
        self.extend_from_slice(source.as_slice());
    }
}

impl From<Vec<u8>> for CompactBytes {
    #[inline]
    fn from(mut value: Vec<u8>) -> Self {
        if value.is_empty() {
            let inline = InlineBytes::empty();
            return CompactBytes { inline };
        }

        // Deconstruct the Vec so we can convert to a `CompactBytes` in constant time.
        let (ptr, len, cap) = (value.as_mut_ptr(), value.len(), value.capacity());
        // SAFETY: We checked above, and returned early, if the `Vec` was empty, thus we know this
        // pointer is not null.
        let ptr = unsafe { NonNull::new_unchecked(ptr) };
        // Forget the original Vec so it's underlying buffer does not get dropped.
        std::mem::forget(value);

        let heap = HeapBytes { ptr, len, cap };
        CompactBytes {
            heap: ManuallyDrop::new(heap),
        }
    }
}

impl serde::Serialize for CompactBytes {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        self.as_slice().serialize(serializer)
    }
}

impl<'de> serde::Deserialize<'de> for CompactBytes {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        deserialize_compact_bytes(deserializer)
    }
}

fn deserialize_compact_bytes<'de: 'a, 'a, D: serde::Deserializer<'de>>(
    deserializer: D,
) -> Result<CompactBytes, D::Error> {
    struct CompactBytesVisitor;

    impl<'a> serde::de::Visitor<'a> for CompactBytesVisitor {
        type Value = CompactBytes;

        fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
            formatter.write_str("bytes")
        }

        fn visit_seq<A: serde::de::SeqAccess<'a>>(
            self,
            mut seq: A,
        ) -> Result<Self::Value, A::Error> {
            let mut bytes = CompactBytes::default();
            if let Some(capacity_hint) = seq.size_hint() {
                bytes.reserve(capacity_hint);
            }

            while let Some(elem) = seq.next_element::<u8>()? {
                bytes.push(elem)
            }

            Ok(bytes)
        }

        fn visit_borrowed_bytes<E: serde::de::Error>(self, v: &'a [u8]) -> Result<Self::Value, E> {
            Ok(CompactBytes::new(v))
        }

        fn visit_bytes<E: serde::de::Error>(self, v: &[u8]) -> Result<Self::Value, E> {
            Ok(CompactBytes::new(v))
        }
    }

    deserializer.deserialize_bytes(CompactBytesVisitor)
}

#[repr(C, align(8))]
#[derive(Copy, Clone)]
struct InlineBytes {
    buffer: [u8; CompactBytes::MAX_INLINE],
    data: u8,
}

impl InlineBytes {
    /// Create an [`InlineBytes`] from the provided slice.
    ///
    /// Safety:
    /// * `slice` must have a length less than or equal to [`CompactBytes::MAX_INLINE`].
    ///
    #[inline]
    pub unsafe fn new(slice: &[u8]) -> Self {
        debug_assert!(slice.len() <= CompactBytes::MAX_INLINE);

        let len = slice.len();
        let mut buffer = [0u8; CompactBytes::MAX_INLINE];

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
        let buffer = [0u8; CompactBytes::MAX_INLINE];

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
    /// * `new_len` must be less than or equal to [`CompactBytes::MAX_INLINE`].
    /// * `new_len` must be less than or equal to capacity.
    /// * The bytes at `old_len..new_len` must be initialized.
    ///
    unsafe fn set_len(&mut self, new_len: usize) {
        debug_assert!(new_len <= CompactBytes::MAX_INLINE);
        self.data = INLINE_MASK | (new_len as u8);
    }
}

#[repr(C)]
struct HeapBytes {
    ptr: NonNull<u8>,
    len: usize,
    cap: usize,
}

impl HeapBytes {
    #[inline]
    pub fn new(slice: &[u8]) -> Self {
        let len = slice.len();
        let cap = len.max(CompactBytes::MIN_HEAP);

        debug_assert!(cap <= CompactBytes::MAX_HEAP, "too large of allocation");
        let ptr = Self::alloc_ptr(cap);

        unsafe { ptr.as_ptr().copy_from_nonoverlapping(slice.as_ptr(), len) };

        HeapBytes { ptr, len, cap }
    }

    pub fn with_capacity(capacity: usize) -> Self {
        assert!(
            capacity <= CompactBytes::MAX_HEAP,
            "too large of allocation"
        );

        let len = 0;
        let cap = capacity.max(CompactBytes::MIN_HEAP);
        let ptr = Self::alloc_ptr(cap);

        HeapBytes {
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

        // Always allocate at least "4 usize" amount of bytes.
        let new_capacity = new_capacity.max(CompactBytes::MIN_HEAP);

        // Already at the appropriate size!
        if new_capacity == self.cap {
            return Ok(new_capacity);
        }

        let cur_layout = Self::layout(self.cap);
        let new_layout = Self::layout(new_capacity);

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
        Self::dealloc_ptr(self.ptr, self.cap);
    }

    #[inline]
    fn alloc_ptr(capacity: usize) -> NonNull<u8> {
        let layout = Self::layout(capacity);
        debug_assert!(layout.size() > 0);

        // SAFETY: We ensure that the layout is not zero sized, by enforcing a minimum size.
        let ptr = unsafe { alloc::alloc(layout) };

        NonNull::new(ptr).expect("failed to allocate HeapRow")
    }

    #[inline]
    fn dealloc_ptr(ptr: NonNull<u8>, capacity: usize) {
        let layout = Self::layout(capacity);

        // SAFETY:
        // * The pointer was allocated via this allocator.
        // * We used the same layout when allocating.
        unsafe { alloc::dealloc(ptr.as_ptr(), layout) };
    }

    #[inline(always)]
    fn layout(capacity: usize) -> alloc::Layout {
        debug_assert!(capacity > 0, "tried to allocate a HeapRow with 0 capacity");
        alloc::Layout::array::<u8>(capacity).expect("valid capacity")
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

impl Drop for HeapBytes {
    fn drop(&mut self) {
        self.dealloc()
    }
}

#[cfg(test)]
mod test {
    use proptest::prelude::*;
    use test_case::test_case;
    use test_strategy::proptest;

    use super::{CompactBytes, HeapBytes};

    #[test]
    fn test_bitcode() {
        let obj = CompactBytes::new(b"hello world");
        let encoded = bitcode::serialize(&obj).unwrap();
        let decoded: CompactBytes = bitcode::deserialize(&encoded).unwrap();
        assert_eq!(obj.as_slice(), decoded.as_slice());
    }

    #[test]
    fn test_empty() {
        let obj = const { CompactBytes::empty() };
        assert_eq!(obj.as_slice(), [0u8; 0].as_slice());
        assert!(obj.is_empty());
        assert!(!obj.spilled())
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_discriminant() {
        let mut buf = vec![0u8; 32];
        let heap = HeapBytes {
            ptr: unsafe { std::ptr::NonNull::new_unchecked(buf.as_mut_ptr()) },
            len: 0,
            cap: usize::MAX >> 1,
        };
        let repr = CompactBytes {
            heap: std::mem::ManuallyDrop::new(heap),
        };
        assert!(repr.spilled());
        // mem::forget the repr since it's underlying buffer is shared.
        std::mem::forget(repr);

        let bad_heap = HeapBytes {
            ptr: unsafe { std::ptr::NonNull::new_unchecked(buf.as_mut_ptr()) },
            len: 0,
            cap: usize::MAX,
        };
        let repr = CompactBytes {
            heap: std::mem::ManuallyDrop::new(bad_heap),
        };
        // This will identify as inline since the MSB is 1.
        assert!(!repr.spilled());
        // mem::forget the repr since it's underlying buffer is shared.
        std::mem::forget(repr);
    }

    #[test_case(&[], 0 ; "empty")]
    #[test_case(b"hello world", 11 ; "short")]
    #[test_case(b"can fit 23 bytes inline", 23 ; "max_inline")]
    #[test_case(b"24 bytes and will spill!", 24 ; "first_spill")]
    #[test_case(b"i am very large and will spill to the heap", 42 ; "heap")]
    fn smoketest_row(slice: &[u8], expected_len: usize) {
        let repr = CompactBytes::new(slice);

        assert_eq!(repr.len(), expected_len);
        assert_eq!(repr.as_slice(), slice);
        assert_eq!(repr.spilled(), expected_len > CompactBytes::MAX_INLINE);
    }

    #[test_case(&[], &[] ; "empty_empty")]
    #[test_case(&[], &[1, 2, 3, 4] ; "empty_inline")]
    #[test_case(&[], b"once extended I will end up on the heap" ; "empty_heap")]
    #[test_case(&[1, 2], &[3, 4] ; "inline_inline")]
    #[test_case(&[1, 2, 3, 4], b"i am some more bytes, i will be on the heap, woohoo!" ; "inline_heap")]
    #[test_case(b"this row will start on the heap because it's large", b"and this will keep it on the heap" ; "heap_heap")]
    fn smoketest_extend(initial: &[u8], other: &[u8]) {
        let mut repr = CompactBytes::new(initial);
        repr.extend_from_slice(other);

        let mut control = initial.to_vec();
        control.extend_from_slice(other);

        assert_eq!(repr.len(), control.len());
        assert_eq!(repr.as_slice(), control.as_slice());
    }

    #[test_case(&[] ; "empty")]
    #[test_case(b"i am smol" ; "inline")]
    #[test_case(b"i am large and will end up on the heap" ; "heap")]
    fn smoketest_clear(initial: &[u8]) {
        let mut repr = CompactBytes::new(initial);
        let capacity = repr.capacity();
        assert_eq!(repr.as_slice(), initial);

        repr.clear();

        assert!(repr.as_slice().is_empty());
        assert_eq!(repr.len(), 0);

        // The capacity should not change after clearing.
        assert_eq!(repr.capacity(), capacity);
    }

    #[test_case(&[] ; "empty")]
    #[test_case(b"smol" ; "inline")]
    #[test_case(b"large large large large large large" ; "heap")]
    fn smoketest_clone(initial: &[u8]) {
        let repr_a = CompactBytes::new(initial);
        let repr_b = repr_a.clone();

        assert_eq!(repr_a.len(), repr_b.len());
        assert_eq!(repr_a.capacity(), repr_b.capacity());
        assert_eq!(repr_a.as_slice(), repr_b.as_slice());
    }

    #[test_case(&[], &[], false ; "empty_empty")]
    #[test_case(&[], b"hello", false ; "empty_inline")]
    #[test_case(&[], b"I am long and will be on the heap", true ; "empty_heap")]
    #[test_case(b"short", &[], false ; "inline_empty")]
    #[test_case(b"hello", b"world", false ; "inline_inline")]
    #[test_case(b"i am short", b"I am long and will be on the heap", true ; "inline_heap")]
    fn smoketest_clone_from(a: &[u8], b: &[u8], should_reallocate: bool) {
        let mut a = CompactBytes::new(a);
        let a_capacity = a.capacity();
        let a_pointer = a.as_slice().as_ptr();

        let b = CompactBytes::new(b);

        // If there is enough capacity in `a`, it's buffer should get re-used.
        a.clone_from(&b);

        assert_eq!(a.capacity() != a_capacity, should_reallocate);
        assert_eq!(a.as_slice().as_ptr() != a_pointer, should_reallocate);
    }

    #[test_case(vec![] ; "empty")]
    #[test_case(vec![0, 1, 2, 3, 4] ; "inline")]
    #[test_case(b"I am long and will be on the heap, yada yada yada".to_vec() ; "heap")]
    fn smoketest_from_vec(initial: Vec<u8>) {
        let control = initial.clone();
        let pointer = initial.as_ptr();
        let repr = CompactBytes::from(initial);

        assert_eq!(control.len(), repr.len());
        assert_eq!(control.as_slice(), repr.as_slice());

        // We do not eagerly inline, except if the Vec is empty.
        assert_eq!(repr.spilled(), !control.is_empty());
        // The allocation of the Vec should get re-used.
        assert_eq!(repr.as_ptr() == pointer, !control.is_empty());
    }

    #[test]
    fn test_cloning_inlines() {
        let mut c = CompactBytes::with_capacity(48);
        c.push(42);

        assert_eq!(c.as_slice(), &[42]);
        assert_eq!(c.capacity(), 48);
        assert!(c.spilled());

        let clone = c.clone();
        assert_eq!(clone.as_slice(), &[42]);
        assert_eq!(clone.capacity(), CompactBytes::MAX_INLINE);
        assert!(!clone.spilled());
    }

    #[test]
    fn test_cloning_drops_excess_capacity() {
        let mut c = CompactBytes::with_capacity(48);
        c.extend_from_slice(&[42; 32]);

        assert_eq!(c.as_slice(), &[42; 32]);
        assert_eq!(c.capacity(), 48);
        assert_eq!(c.len(), 32);
        assert!(c.spilled());

        let clone = c.clone();
        assert_eq!(clone.as_slice(), &[42; 32]);
        assert_eq!(clone.capacity(), 32);
        assert_eq!(clone.capacity(), clone.len());
        assert!(clone.spilled());
    }

    #[proptest]
    #[cfg_attr(miri, ignore)]
    fn proptest_row(initial: Vec<u8>) {
        let repr = CompactBytes::new(&initial);

        prop_assert_eq!(repr.as_slice(), initial.as_slice());
        prop_assert_eq!(repr.len(), initial.len());
    }

    #[proptest]
    #[cfg_attr(miri, ignore)]
    fn proptest_extend(initial: Vec<u8>, other: Vec<u8>) {
        let mut repr = CompactBytes::new(&initial);
        repr.extend_from_slice(other.as_slice());

        let mut control = initial;
        control.extend_from_slice(other.as_slice());

        prop_assert_eq!(repr.as_slice(), control.as_slice());
        prop_assert_eq!(repr.len(), control.len());
    }

    #[proptest]
    #[cfg_attr(miri, ignore)]
    fn proptest_clear(initial: Vec<u8>) {
        let mut repr = CompactBytes::new(&initial);
        let capacity = repr.capacity();

        repr.clear();
        assert!(repr.as_slice().is_empty());
        assert_eq!(repr.len(), 0);

        // Capacity should not have changed after clear.
        assert_eq!(repr.capacity(), capacity);
    }

    #[proptest]
    #[cfg_attr(miri, ignore)]
    fn proptest_clear_then_extend(initial: Vec<u8>, a: Vec<u8>) {
        let mut repr = CompactBytes::new(&initial);
        let capacity = repr.capacity();
        let pointer = repr.as_slice().as_ptr();

        repr.clear();
        assert!(repr.as_slice().is_empty());
        assert_eq!(repr.len(), 0);

        // Capacity should not have changed after clear.
        assert_eq!(repr.capacity(), capacity);

        repr.extend_from_slice(&a);
        assert_eq!(repr.as_slice(), &a);
        assert_eq!(repr.len(), a.len());

        // If we originall had capacity for the new extension, we should not re-allocate.
        if a.len() < capacity {
            assert_eq!(repr.capacity(), capacity);
            assert_eq!(repr.as_slice().as_ptr(), pointer);
        }
    }

    #[proptest]
    #[cfg_attr(miri, ignore)]
    fn proptest_clone(initial: Vec<u8>) {
        let repr_a = CompactBytes::new(&initial);
        let repr_b = repr_a.clone();

        assert_eq!(repr_a.len(), repr_b.len());
        assert_eq!(repr_a.capacity(), repr_b.capacity());
        assert_eq!(repr_a.as_slice(), repr_b.as_slice());
    }

    #[proptest]
    #[cfg_attr(miri, ignore)]
    fn proptest_from_vec(initial: Vec<u8>) {
        let control = initial.clone();
        let pointer = initial.as_ptr();
        let repr = CompactBytes::from(initial);

        assert_eq!(control.len(), repr.len());
        assert_eq!(control.as_slice(), repr.as_slice());

        // We do not eagerly inline, except if the Vec is empty.
        assert_eq!(repr.spilled(), !control.is_empty());
        // The allocation of the Vec should get re-used.
        assert_eq!(repr.as_ptr() == pointer, !control.is_empty());
    }

    #[proptest]
    #[cfg_attr(miri, ignore)]
    fn proptest_serde(initial: Vec<u8>) {
        let repr = CompactBytes::new(&initial);

        let (repr_json, ctrl_json) = match (
            serde_json::to_string(&repr),
            serde_json::to_string(&initial),
        ) {
            (Ok(r), Ok(c)) => (r, c),
            (Err(_), Err(_)) => return Ok(()),
            (r, c) => panic!("Got mismatched results when serializing {r:?}, {c:?}"),
        };

        prop_assert_eq!(&repr_json, &ctrl_json);

        let (repr_rnd_trip, ctrl_rnd_trip): (CompactBytes, Vec<u8>) = match (
            serde_json::from_str(&repr_json),
            serde_json::from_str(&ctrl_json),
        ) {
            (Ok(r), Ok(c)) => (r, c),
            (Err(_), Err(_)) => return Ok(()),
            (r, c) => panic!("Got mismatched results {r:?}, {c:?}"),
        };

        prop_assert_eq!(&repr, &repr_rnd_trip);
        prop_assert_eq!(repr_rnd_trip, ctrl_rnd_trip);
    }
}
