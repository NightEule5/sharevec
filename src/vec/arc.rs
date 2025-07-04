// Copyright 2024 - Strixpyrr
// SPDX-License-Identifier: Apache-2.0

use alloc::alloc::Global;
use alloc::sync::Arc;
use core::alloc::Allocator;
use core::marker::PhantomData;
use core::mem::ManuallyDrop;
use core::ptr;
use core::ptr::NonNull;
use crate::raw::RawVec;

/// A contiguous, growable array type, with heap-allocated, reference-counted contents. Unlike
/// [`Vec`], it can be cheaply cloned in *O*(1) time, sharing the contents between clones. As a
/// consequence, cloning is allowed even when the element type lacks [`Clone`].
///
/// Vectors containing a *unique* reference can be used as a [`Vec`] would be, with *O*(1) index and
/// pop operations, and an amortized *O*(1) push operation. In addition, unlike [`Vec`], it can be
/// cheaply cloned in *O*(1) time, sharing its memory with its clones.
///
/// Vectors containing a *shared* reference become clone-on-write. The pop operation is still *O*(1),
/// cloning the removed element, but any other modifying operation requires an *O*(*n*) clone of the
/// vector contents. Thus, when shared, the element type must implement [`Clone`] for modification.
/// As with [`Arc`], the vector may also be downgraded to a *weak* reference, preventing another
/// referring vector from resizing or deallocating its capacity but otherwise allowing it to act as
/// unique.
///
/// This type is thread-safe, and can safely share memory across threads; it implements [`Send`] and
/// [`Sync`] if [`T`] also implements these. Unless this is an explicit requirement, it is usually
/// preferable to use [`RcVec`] instead, as atomic operations are more expensive than simple memory
/// accesses.
///
/// # Uniqueness
///
/// See the module-level [uniqueness](super#uniqueness) section.
///
/// # Examples
///
/// Use [`new`](Self::new) to create a new vector:
///
/// ```
/// use sharevec::vec::arc::Vec;
///
/// let vec: Vec<i32> = Vec::new();
/// ```
///
/// You can [`try_push`] to or [`pop`] from the end of the vector:
///
/// ```
/// use sharevec::vec::arc::Vec;
///
/// let mut vec: Vec<i32> = Vec::with_capacity(10);
/// vec.try_push(1).unwrap();
/// vec.try_push(2).unwrap();
/// assert_eq!(vec.pop(), Some(2));
/// ```
///
/// ...unless it's been cloned and has memory allocated:
///
/// ```should_panic
/// use sharevec::vec::arc::Vec;
///
/// let mut vec: Vec<i32> = Vec::with_capacity(10);
/// let shared = vec.clone();
/// // Panic!
/// vec.try_push(1).unwrap();
/// vec.try_push(2).unwrap();
/// ```
///
/// [`Clone`]able elements may be [`pop`]ped from a shared vector:
///
/// ```
/// use sharevec::vec::arc::Vec;
///
/// let mut vec: Vec<i32> = Vec::from(&[1, 2, 3]);
/// let mut shared = vec.clone();
///
/// // The same value was popped from both vectors
/// let first = vec.pop().unwrap();
/// let second = shared.pop().unwrap();
/// assert_eq!(first, second);
/// ```
///
/// [`Vec`]: alloc::vec::Vec
/// [`RcVec`]: crate::rc::vec::RcVec
/// [`try_push`]: Self::push
/// [`pop`]: Self::pop
pub type Vec<T, A = Global> = super::Vec<T, true, A>;

/// An iterator over a drained range in [`Vec`], obtained by [`Vec::drain`]/[`try_drain`] or
/// [`Unique::drain`].
///
/// [`try_drain`]: ArrayVec::try_drain
pub type Drain<'a, T, A = Global> = super::Drain<'a, T, A, true>;

/// An iterator which moves or clones the contents out of an [`Vec`], obtained by
/// [`Vec::into_iter`]/[`try_into_iter`] or [`Unique::into_iter`].
///
/// [`try_into_iter`]: ArrayVec::try_into_iter
pub type IntoIter<T, A = Global> = super::IntoIter<T, A, true>;

/// A mutable view over an [`Vec`] with a unique reference, obtained by [`Vec::unique`] or
/// [`Vec::as_unique`].
///
/// This type provides a compile-time guarantee that the vector holds a unique reference[^weak] for
/// the lifetime of the borrow. Once this wrapper is dropped, modifying the vector may fail. This is
/// possible because the compiler does not allow multiple references to a mutably-referenced value.
/// To clone the vector and make it immutable, it must be borrowed, which the compiler does not
/// allow while this type holds its mutable reference.
///
/// [^weak]: for the purposes of this guarantee, no weak references are allowed. This is because a
/// weak reference could be upgraded to a strong reference while this wrapper still exists, enabling
/// mutability on a shared vector.
pub type Unique<'a, T, A = Global> = super::Unique<'a, T, A, true>;

/// A non-owning reference to the contents of a [`Vec`], obtained by [`Vec::demote`] or
/// [`Unique::demote`].
pub type Weak<T, A = Global> = super::Weak<T, A, true>;

impl<T> Vec<T> {
	/// Creates a vector directly from a pointer, a length, and a capacity.
	///
	/// # Safety
	///
	/// This is highly unsafe, as many invariants aren't checked:
	///
	/// - The pointer must have been allocated by the [global](Global) allocator.
	/// - `T` must strictly have the same alignment as the pointer's allocated alignment.
	/// - The pointer's allocated size must be exactly equal to the size of `T` times the `capacity`
	///   plus an additional prefix of `3` [`usize`] words (same layout as the `Arc<(usize, [T; N])>`
	///   inner pointer).
	/// - The `length` must be less than or equal to the `capacity`.
	/// - The first `length` values must be properly initialized for type `T`.
	///
	/// These requirements are always upheld by any pointer allocated by `Arc<(usize, [T; N])>`/`Arc<(usize, [T])>`
	/// and, by extension, any of the `Arc`-based vector types in this crate. A similar `Rc`-based
	/// pointer may be allowed if the above invariants are upheld, with the additional requirement
	/// that it must be a fully unique reference to change it to non-atomic. Other sources are
	/// **not** allowed.
	///
	/// Violating these may cause corruption of the allocator's internal data structures.
	///
	/// The ownership of the pointer is effectively moved to the vector, which may then deallocate,
	/// reallocate, modify the reference counts or contents of memory pointed to by the pointer. The
	/// pointer therefore cannot be used after calling this function.
	///
	/// # Examples
	///
	/// See the example at [`into_raw_parts`](Self::into_raw_parts#example).
	pub unsafe fn from_raw_parts(ptr: *mut T, length: usize, capacity: usize) -> Self {
		Self::from_raw_parts_in(ptr, length, capacity, Global)
	}

	/// Creates a vector directly from a [`NonNull`] pointer, a length, and a capacity.
	///
	/// # Safety
	///
	/// This is highly unsafe, as many invariants aren't checked:
	///
	/// - The pointer must have been allocated by the [global](Global) allocator.
	/// - `T` must strictly have the same alignment as the pointer's allocated alignment.
	/// - The pointer's allocated size must be exactly equal to the size of `T` times the `capacity`
	///   plus an additional prefix of `3` [`usize`] words (same layout as the `Arc<(usize, [T; N])>`
	///   inner pointer).
	/// - The `length` must be less than or equal to the `capacity`.
	/// - The first `length` values must be properly initialized for type `T`.
	///
	/// These requirements are always upheld by any pointer allocated by `Arc<(usize, [T; N])>`/`Arc<(usize, [T])>`
	/// and, by extension, any of the `Arc`-based vector types in this crate. A similar `Rc`-based
	/// pointer may be allowed if the above invariants are upheld, with the additional requirement
	/// that it must be a fully unique reference to change it to non-atomic. Other sources are
	/// **not** allowed.
	///
	/// Violating these may cause corruption of the allocator's internal data structures.
	///
	/// The ownership of the pointer is effectively moved to the vector, which may then deallocate,
	/// reallocate, modify the reference counts or contents of memory pointed to by the pointer. The
	/// pointer therefore cannot be used after calling this function.
	///
	/// # Examples
	///
	/// See the example at [`into_parts`](Self::into_parts#examples).
	pub unsafe fn from_parts(ptr: NonNull<T>, length: usize, capacity: usize) -> Self {
		Self::from_parts_in(ptr, length, capacity, Global)
	}
}

impl<T, A: Allocator> Vec<T, A> {
	/// Creates a vector directly from a pointer, a length, a capacity, and an allocator.
	///
	/// # Safety
	///
	/// This is highly unsafe, as many invariants aren't checked:
	///
	/// - The pointer must be [*currently allocated*] allocated by the specified allocator.
	/// - `T` must strictly have the same alignment as the pointer's allocated alignment.
	/// - The pointer's allocated size must be exactly equal to the size of `T` times the `capacity`
	///   plus an additional prefix of `3` [`usize`] words (same layout as the `Arc<(usize, [T; N])>`
	///   inner pointer).
	/// - The `length` must be less than or equal to the `capacity`.
	/// - The first `length` values must be properly initialized for type `T`.
	/// - The `capacity` must [*fit*] the layout size that the pointer was allocated with.
	///
	/// These requirements are always upheld by any pointer allocated by `Arc<(usize, [T; N])>`/`Arc<(usize, [T])>`
	/// and, by extension, any of the `Arc`-based vector types in this crate. A similar `Rc`-based
	/// pointer may be allowed if the above invariants are upheld, with the additional requirement
	/// that it must be a fully unique reference to change it to non-atomic. Other sources are
	/// **not** allowed.
	///
	/// Violating these may cause corruption of the allocator's internal data structures.
	///
	/// The ownership of the pointer is effectively moved to the vector, which may then deallocate,
	/// reallocate, modify the reference counts or contents of memory pointed to by the pointer. The
	/// pointer therefore cannot be used after calling this function.
	///
	/// [*currently allocated*]: crate::alloc::Allocator#currently-allocated-memory
	/// [*fit*]: crate::alloc::Allocator#memory-fitting
	///
	/// # Examples
	///
	/// See the example at [`into_raw_parts_with_alloc`](Self::into_raw_parts_with_alloc#examples).
	pub unsafe fn from_raw_parts_in(ptr: *mut T, length: usize, capacity: usize, alloc: A) -> Self {
		Self {
			inner: RawVec::<[_], _>::from_raw_parts(ptr, capacity, alloc),
			len: length,
		}
	}

	/// Creates a vector directly from a [`NonNull`] pointer, a length, a capacity, and an allocator.
	///
	/// # Safety
	///
	/// This is highly unsafe, as many invariants aren't checked:
	///
	/// - The pointer must be [*currently allocated*] allocated by the specified allocator.
	/// - `T` must strictly have the same alignment as the pointer's allocated alignment.
	/// - The pointer's allocated size must be exactly equal to the size of `T` times the `capacity`
	///   plus an additional prefix of `3` [`usize`] words (same layout as the `Arc<(usize, [T; N])>`
	///   inner pointer).
	/// - The `length` must be less than or equal to the `capacity`.
	/// - The first `length` values must be properly initialized for type `T`.
	/// - The `capacity` must [*fit*] the layout size that the pointer was allocated with.
	///
	/// These requirements are always upheld by any pointer allocated by `Arc<(usize, [T; N])>`/`Arc<(usize, [T])>`
	/// and, by extension, any of the `Arc`-based vector types in this crate. A similar `Rc`-based
	/// pointer may be allowed if the above invariants are upheld, with the additional requirement
	/// that it must be a fully unique reference to change it to non-atomic. Other sources are
	/// **not** allowed.
	///
	/// Violating these may cause corruption of the allocator's internal data structures.
	///
	/// The ownership of the pointer is effectively moved to the vector, which may then deallocate,
	/// reallocate, modify the reference counts or contents of memory pointed to by the pointer. The
	/// pointer therefore cannot be used after calling this function.
	///
	/// [*currently allocated*]: crate::alloc::Allocator#currently-allocated-memory
	/// [*fit*]: crate::alloc::Allocator#memory-fitting
	///
	/// # Examples
	///
	/// See the example at [`into_parts_with_alloc`](Self::into_parts_with_alloc#examples).
	pub unsafe fn from_parts_in(ptr: NonNull<T>, length: usize, capacity: usize, alloc: A) -> Self {
		Self {
			inner: RawVec::<[_], _>::from_non_null(ptr, capacity, alloc),
			len: length,
		}
	}

	/// Decomposes the vector into its raw components: pointer, length, and capacity.
	///
	/// Returns the raw pointer to the underlying data, and the length of the vector. These are the
	/// same arguments in the same order as [`from_raw_parts`].
	///
	/// The caller is responsible for the memory previously managed by the vector. To manage this
	/// memory, the raw pointer and length must be converted back to an `Arc`-based type listed
	/// below. It **cannot** be modified before this conversion.
	/// - an atomic `Vec` of the same capacity with [`from_raw_parts`]
	/// - an atomic `ArrayVec` of the same capacity with [`AcArrayVec::from_raw_parts`]
	// - an `Arc<[T; N]>` or `Arc<[T]>`, **only** if the original vector is full
	///
	/// [`from_raw_parts`]: Self::from_raw_parts
	/// [`ArcArrayVec::from_raw_parts`]: crate::array::vec::arc::ArrayVec::from_raw_parts
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::arc::Vec;
	///
	/// let vec = Vec::from([1, 2, 3]);
	/// let (ptr, len, cap) = vec.into_raw_parts();
	/// let rebuilt = unsafe {
	///     // The pointer can be transmuted to a compatible type. Care must be
	///     // taken that any data that could be represented by the old type is
	///     // still valid in the new type, as sharing is possible. Note that the
	///     // contents themselves must never be modified here.
	///     let ptr = ptr as *mut u32;
	///
	///     Vec::from_raw_parts(ptr, len, cap)
	/// };
	/// assert_eq!(rebuilt, [1, 2, 3]);
	/// ```
	#[must_use = "losing the pointer will leak memory"]
	pub fn into_raw_parts(self) -> (*mut T, usize, usize) {
		let (ptr, len, cap, _) = self.into_raw_parts_with_alloc();
		(ptr, len, cap)
	}

	/// Decomposes the vector into its raw components: `NonNull` pointer, length, and capacity.
	///
	/// Returns the `NonNull` pointer to the underlying data, and the length of the vector. These are
	/// the same arguments in the same order as [`from_parts`].
	///
	/// The caller is responsible for the memory previously managed by the vector. To manage this
	/// memory, the `NonNull` pointer and length must be converted back to an `Arc`-based type listed
	/// below. It **cannot** be modified before this conversion.
	/// - an atomic `Vec` of the same capacity with [`from_parts`]
	/// - an atomic `ArrayVec` of the same capacity with [`ArcArrayVec::from_parts`]
	// - an `Arc<[T; N]>` or `Arc<[T]>`, **only** if the original vector is full
	///
	/// [`from_parts`]: Self::from_parts
	/// [`ArcArrayVec::from_parts`]: crate::array::vec::arc::ArrayVec::from_parts
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::arc::Vec;
	///
	/// let vec = Vec::from([1, 2, 3]);
	/// let (ptr, len, cap) = vec.into_parts();
	/// let rebuilt = unsafe {
	///     // The pointer can be transmuted to a compatible type. Care must be
	///     // taken that any data that could be represented by the old type is
	///     // still valid in the new type, as sharing is possible. Note that the
	///     // contents themselves must never be modified here.
	///     let ptr = ptr.cast::<u32>();
	///
	///     Vec::from_parts(ptr, len, cap)
	/// };
	/// assert_eq!(rebuilt, [1, 2, 3]);
	/// ```
	#[must_use = "losing the pointer will leak memory"]
	pub fn into_parts(self) -> (NonNull<T>, usize, usize) {
		let (ptr, len, cap, _) = self.into_parts_with_alloc();
		(ptr, len, cap)
	}

	/// Decomposes the vector into its raw components: pointer, length, capacity, and allocator.
	///
	/// Returns the raw pointer to the underlying data, the length of the vector, and the allocator.
	/// These are the same arguments in the same order as [`from_raw_parts_in`].
	///
	/// The caller is responsible for the memory previously managed by the vector. To manage this
	/// memory, the raw pointer, length, and allocator must be converted back to an `Arc`-based type
	/// listed below. It **cannot** be modified before this conversion.
	/// - an atomic `Vec` of the same capacity with [`from_raw_parts_in`]
	/// - an atomic `ArrayVec` of the same capacity with [`ArcArrayVec::from_raw_parts_in`]
	// - an `Arc<[T; N]>` or `Arc<[T]>`, **only** if the original vector is full
	///
	/// [`from_raw_parts_in`]: Self::from_raw_parts_in
	/// [`ArcArrayVec::from_raw_parts_in`]: crate::array::vec::arc::ArrayVec::from_raw_parts_in
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::arc::Vec;
	///
	/// let vec = Vec::from([1, 2, 3]);
	/// let (ptr, len, cap, alloc) = vec.into_raw_parts_with_alloc();
	/// let rebuilt = unsafe {
	///     // The pointer can be transmuted to a compatible type. Care must be
	///     // taken that any data that could be represented by the old type is
	///     // still valid in the new type, as sharing is possible. Note that the
	///     // contents themselves must never be modified here.
	///     let ptr = ptr as *mut u32;
	///
	///     Vec::from_raw_parts_in(ptr, len, cap, alloc)
	/// };
	/// assert_eq!(rebuilt, [1, 2, 3]);
	/// ```
	#[must_use = "losing the pointer will leak memory"]
	pub fn into_raw_parts_with_alloc(self) -> (*mut T, usize, usize, A) {
		let (ptr, len, cap, alloc) = self.into_parts_with_alloc();
		(ptr.as_ptr(), len, cap, alloc)
	}

	/// Decomposes the vector into its raw components: `NonNull` pointer, length, capacity, and
	/// allocator.
	///
	/// Returns the `NonNull` pointer to the underlying data, the length of the vector, and the
	/// allocator. These are the same arguments in the same order as [`from_parts_in`].
	///
	/// The caller is responsible for the memory previously managed by the vector. To manage this
	/// memory, the `NonNull` pointer, length, and allocator must be converted back to an `Arc`-based
	/// type listed below. It **cannot** be modified before this conversion.
	/// - an atomic `Vec` of the same capacity with [`from_parts_in`]
	/// - an atomic `ArrayVec` of the same capacity with [`ArcArrayVec::from_parts_in`]
	// - an `Arc<[T; N]>` or `Arc<[T]>`, **only** if the original vector is full
	///
	/// [`from_parts_in`]: Self::from_parts_in
	/// [`ArcArrayVec::from_parts_in`]: crate::array::vec::arc::ArrayVec::from_parts_in
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::arc::Vec;
	///
	/// let vec = Vec::from([1, 2, 3]);
	/// let (ptr, len, cap, alloc) = vec.into_parts_with_alloc();
	/// let rebuilt = unsafe {
	///     // The pointer can be transmuted to a compatible type. Care must be
	///     // taken that any data that could be represented by the old type is
	///     // still valid in the new type, as sharing is possible. Note that the
	///     // contents themselves must never be modified here.
	///     let ptr = ptr.cast::<u32>();
	///
	///     Vec::from_parts_in(ptr, len, cap, alloc)
	/// };
	/// assert_eq!(rebuilt, [1, 2, 3]);
	/// ```
	#[must_use = "losing the pointer will leak memory"]
	pub fn into_parts_with_alloc(self) -> (NonNull<T>, usize, usize, A) {
		let mut this = ManuallyDrop::new(self);
		let ptr = this.as_non_null();
		let len = this.len();
		let cap = this.capacity();
		// Safety: the allocator is moved out of `self`, and never touched again.
		let alloc = unsafe {
			ptr::read(this.inner.allocator())
		};
		(ptr, len, cap, alloc)
	}

	/// Returns a weak reference to the allocation. This does not count toward strong sharing, but
	/// guarantees that the underlying memory will not be deallocated.
	///
	/// Equivalent to [`Arc::downgrade`].
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::arc::Vec;
	///
	/// let mut vec = Vec::new();
	/// let weak_vec = vec.demote();
	///
	/// assert_eq!(vec.try_push(1), Ok(()));
	/// ```
	pub fn demote(&self) -> Weak<T, A>
	where
		A: Clone
	{
		// Clone the allocator first, in case cloning panics. In this case, the
		// weak count is not incremented.
		let alloc = self.allocator().clone();

		if self.inner.is_dangling() {
			Weak::new_in(alloc)
		} else {
			self.inner.weak_inc::<false>();
			let ptr = self.inner.inner_ptr().cast();
			let cap = self.capacity();
			Weak {
				ptr,
				_t: PhantomData,
				cap,
				alloc: ManuallyDrop::new(alloc),
			}
		}
	}
}

impl<T, A: Allocator + Clone> Unique<'_, T, A> {
	/// Consumes the reference, returning a weak reference to the allocation.
	///
	/// Equivalent to [`Arc::downgrade`].
	pub fn demote(self) -> Weak<T, A> {
		self.vec.demote()
	}
}

impl<T, const N: usize, A: Allocator> From<Arc<[T; N], A>> for Vec<T, A> {
	fn from(value: Arc<[T; N], A>) -> Self {
		todo!()
	}
}

impl<T, const N: usize, A: Allocator> TryFrom<Vec<T, A>> for Arc<[T; N], A> {
	type Error = Vec<T, A>;

	fn try_from(value: Vec<T, A>) -> Result<Self, Self::Error> {
		todo!()
	}
}

impl<T, A: Allocator> TryFrom<Arc<[T], A>> for Vec<T, A> {
	type Error = Arc<[T], A>;

	fn try_from(value: Arc<[T], A>) -> Result<Self, Arc<[T], A>> {
		todo!()
	}
}

impl<A: Allocator> From<Arc<str, A>> for Vec<u8, A> {
	fn from(value: Arc<str, A>) -> Self {
		todo!()
	}
}

impl<T, A: Allocator> From<Vec<T, A>> for Arc<[T], A> {
	fn from(value: Vec<T, A>) -> Self {
		todo!()
	}
}
