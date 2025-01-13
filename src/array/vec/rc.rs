// Copyright 2024 - Strixpyrr
// SPDX-License-Identifier: Apache-2.0

use crate::error::Result;
use alloc::{
	alloc::Global,
	rc::Rc,
};
use core::alloc::Allocator;
use core::ptr::NonNull;

/// A contiguous, fixed-capacity array type, with heap-allocated, reference-counted contents. Can be
/// cheaply cloned in *O*(1) time, sharing its contents between clones. As a consequence, cloning is
/// allowed even when the element type lacks [`Clone`].
///
/// Vectors containing a *unique* reference can be used as a [`Vec`] would be, with *O*(1) index and
/// pop operations, but with an *O*(1) push operation within its fixed capacity. In addition, unlike
/// [`Vec`], it can be cheaply cloned in *O*(1) time, sharing its memory with its clones.
///
/// Vectors containing a *shared* reference become clone-on-write. The pop operation is still *O*(1),
/// cloning the removed element, but any other modifying operation requires an *O*(*n*) clone of the
/// vector contents. Thus, when shared, the element type must implement [`Clone`] for modification.
///
/// # Examples
///
/// Use [`new`](Self::new) to create a new vector:
///
/// ```
/// use sharevec::array::vec::rc::ArrayVec;
///
/// let vec: ArrayVec<i32, 8> = ArrayVec::new();
/// ```
///
/// You can [`try_push`] to or [`pop`] from the end of the vector:
///
/// ```
/// use sharevec::array::vec::rc::ArrayVec;
///
/// let mut vec: ArrayVec<i32, 8> = ArrayVec::new();
/// vec.try_push(1).unwrap();
/// vec.try_push(2).unwrap();
/// assert_eq!(vec.pop(), Some(2));
/// ```
///
/// ...unless it's been cloned:
///
/// ```should_panic
/// use sharevec::array::vec::rc::ArrayVec;
///
/// let mut vec: ArrayVec<i32, 8> = ArrayVec::new();
/// let shared = vec.clone();
/// // Panic!
/// vec.try_push(1).unwrap();
/// vec.try_push(2).unwrap();
/// ```
///
/// [`Clone`]able elements may be [`pop`]ped from a shared vector:
///
/// ```
/// use sharevec::array::vec::rc::ArrayVec;
///
/// let mut vec: ArrayVec<i32, 3> = ArrayVec::from(&[1, 2, 3]);
/// let mut shared = vec.clone();
///
/// // The same value was popped from both vectors
/// let first = vec.pop().unwrap();
/// let second = shared.pop().unwrap();
/// assert_eq!(first, second);
/// ```
///
/// [`try_push`]: Self::push
/// [`pop`]: Self::pop
pub type ArrayVec<T, const N: usize, A = Global> = super::ArrayVec<T, N, false, A>;

/// An iterator over a drained range in [`ArrayVec`], obtained by [`ArrayVec::drain`]/[`try_drain`]
/// or [`Unique::drain`].
/// 
/// [`try_drain`]: ArrayVec::try_drain
pub type Drain<'a, T, const N: usize, A = Global> = super::Drain<'a, T, N, A, false>;

/// An iterator which moves or clones the contents out of an [`ArrayVec`], obtained by
/// [`ArrayVec::into_iter`]/[`try_into_iter`] or [`Unique::into_iter`].
///
/// [`try_into_iter`]: ArrayVec::try_into_iter
pub type IntoIter<T, const N: usize, A = Global> = super::IntoIter<T, N, A, false>;

/// A mutable view over an [`ArrayVec`] with a unique reference, obtained by [`ArrayVec::unique`] or
/// [`ArrayVec::as_unique`].
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
pub type Unique<'a, T, const N: usize, A = Global> = super::Unique<'a, T, N, A, false>;

/// A non-owning reference to the contents of an [`ArrayVec`], obtained by [`ArrayVec::demote`] or
/// [`Unique::demote`].
pub type Weak<T, const N: usize, A = Global> = super::Weak<T, N, A, false>;

impl<T, const N: usize> ArrayVec<T, N> {
	/// Creates a vector directly from a pointer and a length.
	///
	/// # Safety
	///
	/// This is highly unsafe, as many invariants aren't checked:
	///
	/// - The pointer must have been allocated by the [global](Global) allocator.
	/// - `T` must strictly have the same alignment as the pointer's allocated alignment.
	/// - The pointer's allocated size must be exactly equal to the size of `T` times `N` plus an
	///   additional prefix of `3` [`usize`] words (same layout as the `Rc<(usize, [T; N])>` inner
	///   pointer).
	/// - The `length` must be less than or equal to `N`.
	/// - The first `length` values must be properly initialized for type `T`.
	///
	/// These requirements are always upheld by any pointer allocated by `Rc<(usize, [T; N])>`/`Rc<(usize, [T])>`
	/// and, by extension, any of the `Rc`-based vector types in this crate. A similar `Arc`-based
	/// pointer may be allowed if the above invariants are upheld, with the additional requirement
	/// that it must be a fully unique reference to change it to atomic. Other sources are **not**
	/// allowed.
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
	pub unsafe fn from_raw_parts(ptr: *mut T, length: usize) -> Self {
		Self::from_raw_parts_in(ptr, length, Global)
	}

	/// Creates a vector directly from a [`NonNull`] pointer and a length.
	///
	/// # Safety
	///
	/// This is highly unsafe, as many invariants aren't checked:
	///
	/// - The pointer must have been allocated by the [global](Global) allocator.
	/// - `T` must strictly have the same alignment as the pointer's allocated alignment.
	/// - The pointer's allocated size must be exactly equal to the size of `T` times `N` plus an
	///   additional prefix of `3` [`usize`] words (same layout as the `Rc<(usize, [T; N])>` inner
	///   pointer).
	/// - The `length` must be less than or equal to `N`.
	/// - The first `length` values must be properly initialized for type `T`.
	///
	/// These requirements are always upheld by any pointer allocated by `Rc<(usize, [T; N])>`/`Rc<(usize, [T])>`
	/// and, by extension, any of the `Rc`-based vector types in this crate. A similar `Arc`-based
	/// pointer may be allowed if the above invariants are upheld, with the additional requirement
	/// that it must be a fully unique reference to change it to atomic. Other sources are **not**
	/// allowed.
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
	pub unsafe fn from_parts(ptr: NonNull<T>, length: usize) -> Self {
		Self::from_parts_in(ptr, length, Global)
	}
}

impl<T, const N: usize, A: Allocator> ArrayVec<T, N, A> {
	/// Creates a vector directly from a pointer, a length, and an allocator.
	///
	/// # Safety
	///
	/// This is highly unsafe, as many invariants aren't checked:
	///
	/// - The pointer must be [*currently allocated*] allocated by the specified allocator.
	/// - `T` must strictly have the same alignment as the pointer's allocated alignment.
	/// - The pointer's allocated size must be exactly equal to the size of `T` times `N` plus an
	///   additional prefix of `3` [`usize`] words (same layout as the `Rc<(usize, [T; N])>` inner
	///   pointer).
	/// - The `length` must be less than or equal to `N`.
	/// - The first `length` values must be properly initialized for type `T`.
	/// - The capacity `N` must [*fit*] the layout size that the pointer was allocated with.
	///
	/// These requirements are always upheld by any pointer allocated by `Rc<(usize, [T; N])>`/`Rc<(usize, [T])>`
	/// and, by extension, any of the `Rc`-based vector types in this crate. A similar `Arc`-based
	/// pointer may be allowed if the above invariants are upheld, with the additional requirement
	/// that it must be a fully unique reference to change it to atomic. Other sources are **not**
	/// allowed.
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
	pub unsafe fn from_raw_parts_in(ptr: *mut T, length: usize, alloc: A) -> Self {
		todo!()
	}

	/// Creates a vector directly from a [`NonNull`] pointer, a length, and an allocator.
	///
	/// # Safety
	///
	/// This is highly unsafe, as many invariants aren't checked:
	///
	/// - The pointer must be [*currently allocated*] allocated by the specified allocator.
	/// - `T` must strictly have the same alignment as the pointer's allocated alignment.
	/// - The pointer's allocated size must be exactly equal to the size of `T` times `N` plus an
	///   additional prefix of `3` [`usize`] words (same layout as the `Rc<(usize, [T; N])>` inner
	///   pointer).
	/// - The `length` must be less than or equal to `N`.
	/// - The first `length` values must be properly initialized for type `T`.
	/// - The capacity `N` must [*fit*] the layout size that the pointer was allocated with.
	///
	/// These requirements are always upheld by any pointer allocated by `Rc<(usize, [T; N])>`/`Rc<(usize, [T])>`
	/// and, by extension, any of the `Rc`-based vector types in this crate. A similar `Arc`-based
	/// pointer may be allowed if the above invariants are upheld, with the additional requirement
	/// that it must be a fully unique reference to change it to atomic. Other sources are **not**
	/// allowed.
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
	pub unsafe fn from_parts_in(ptr: NonNull<T>, length: usize, alloc: A) -> Self {
		todo!()
	}

	/// Decomposes the vector into its raw components: pointer and length.
	///
	/// Returns the raw pointer to the underlying data, and the length of the vector. These are the
	/// same arguments in the same order as [`from_raw_parts`].
	///
	/// The caller is responsible for the memory previously managed by the vector. To manage this
	/// memory, the raw pointer and length must be converted back to an `Rc`-based type listed
	/// below. It **cannot** be modified before this conversion.
	/// - a non-atomic `ArrayVec` of the same capacity with [`from_raw_parts`]
	/// - a non-atomic `Vec` of the same capacity with [`RcVec::from_raw_parts`]
	// - an `Rc<[T; N]>` or `Rc<[T]>`, **only** if the original vector is full
	///
	/// [`from_raw_parts`]: Self::from_raw_parts
	/// [`RcVec::from_raw_parts`]: crate::vec::rc::Vec::from_raw_parts
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let vec = ArrayVec::from([-1, 0, 1]);
	/// let (ptr, len) = vec.into_raw_parts();
	/// let rebuilt = unsafe {
	///     // The pointer can be transmuted to a compatible type. Care must be
	///     // taken that any data that could be represented by the old type is
	///     // still valid in the new type, as sharing is possible. Note that the
	///     // contents themselves must never be modified here.
	///     let ptr = ptr as *mut u32;
	///
	///     ArrayVec::<u32, 3>::from_raw_parts(ptr, len)
	/// };
	/// assert_eq!(rebuilt, [-1i32 as u32, 0, 1]);
	/// ```
	#[must_use = "losing the pointer will leak memory"]
	pub fn into_raw_parts(self) -> (*mut T, usize) {
		todo!()
	}

	/// Decomposes the vector into its raw components: `NonNull` pointer and length.
	///
	/// Returns the `NonNull` pointer to the underlying data, and the length of the vector. These are
	/// the same arguments in the same order as [`from_parts`].
	///
	/// The caller is responsible for the memory previously managed by the vector. To manage this
	/// memory, the `NonNull` pointer and length must be converted back to an `Rc`-based type listed
	/// below. It **cannot** be modified before this conversion.
	/// - a non-atomic `ArrayVec` of the same capacity with [`from_parts`]
	/// - a non-atomic `Vec` of the same capacity with [`RcVec::from_parts`]
	// - an `Rc<[T; N]>` or `Rc<[T]>`, **only** if the original vector is full
	///
	/// [`from_parts`]: Self::from_parts
	/// [`RcVec::from_parts`]: crate::vec::rc::Vec::from_parts
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let vec = ArrayVec::from([1, 2, 3]);
	/// let (ptr, len) = vec.into_parts();
	/// let rebuilt = unsafe {
	///     // The pointer can be transmuted to a compatible type. Care must be
	///     // taken that any data that could be represented by the old type is
	///     // still valid in the new type, as sharing is possible. Note that the
	///     // contents themselves must never be modified here.
	///     let ptr = ptr.cast::<u32>();
	///
	///     ArrayVec::<u32, 3>::from_parts(ptr, len)
	/// };
	/// assert_eq!(rebuilt, [-1i32 as u32, 0, 1]);
	/// ```
	#[must_use = "losing the pointer will leak memory"]
	pub fn into_parts(self) -> (NonNull<T>, usize) {
		todo!()
	}

	/// Decomposes the vector into its raw components: pointer, length, and allocator.
	///
	/// Returns the raw pointer to the underlying data, the length of the vector, and the allocator.
	/// These are the same arguments in the same order as [`from_raw_parts_in`].
	///
	/// The caller is responsible for the memory previously managed by the vector. To manage this
	/// memory, the raw pointer, length, and allocator must be converted back to an `Rc`-based type
	/// listed below. It **cannot** be modified before this conversion.
	/// - a non-atomic `ArrayVec` of the same capacity with [`from_raw_parts_in`]
	/// - a non-atomic `Vec` of the same capacity with [`RcVec::from_raw_parts_in`]
	// - an `Rc<[T; N]>` or `Rc<[T]>`, **only** if the original vector is full
	///
	/// [`from_raw_parts_in`]: Self::from_raw_parts_in
	/// [`RcVec::from_raw_parts_in`]: crate::vec::rc::Vec::from_raw_parts_in
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let vec = ArrayVec::from([1, 2, 3]);
	/// let (ptr, len, alloc) = vec.into_raw_parts_with_alloc();
	/// let rebuilt = unsafe {
	///     // The pointer can be transmuted to a compatible type. Care must be
	///     // taken that any data that could be represented by the old type is
	///     // still valid in the new type, as sharing is possible. Note that the
	///     // contents themselves must never be modified here.
	///     let ptr = ptr as *mut u32;
	///
	///     ArrayVec::<u32, 3>::from_raw_parts_in(ptr, len, alloc)
	/// };
	/// assert_eq!(rebuilt, [-1i32 as u32, 0, 1]);
	/// ```
	#[must_use = "losing the pointer will leak memory"]
	pub fn into_raw_parts_with_alloc(self) -> (*mut T, usize, A) {
		todo!()
	}

	/// Decomposes the vector into its raw components: `NonNull` pointer, length, and allocator.
	///
	/// Returns the `NonNull` pointer to the underlying data, the length of the vector, and the
	/// allocator. These are the same arguments in the same order as [`from_parts_in`].
	///
	/// The caller is responsible for the memory previously managed by the vector. To manage this
	/// memory, the `NonNull` pointer, length, and allocator must be converted back to an `Rc`-based
	/// type listed below. It **cannot** be modified before this conversion.
	/// - a non-atomic `ArrayVec` of the same capacity with [`from_parts_in`]
	/// - a non-atomic `Vec` of the same capacity with [`RcVec::from_parts_in`]
	// - an `Rc<[T; N]>` or `Rc<[T]>`, **only** if the original vector is full
	///
	/// [`from_parts_in`]: Self::from_parts_in
	/// [`RcVec::from_parts_in`]: crate::vec::rc::Vec::from_parts_in
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let vec = ArrayVec::from([1, 2, 3]);
	/// let (ptr, len, alloc) = vec.into_parts_with_alloc();
	/// let rebuilt = unsafe {
	///     // The pointer can be transmuted to a compatible type. Care must be
	///     // taken that any data that could be represented by the old type is
	///     // still valid in the new type, as sharing is possible. Note that the
	///     // contents themselves must never be modified here.
	///     let ptr = ptr.cast::<u32>();
	///
	///     ArrayVec::<u32, 3>::from_parts_in(ptr, len, alloc)
	/// };
	/// assert_eq!(rebuilt, [-1i32 as u32, 0, 1]);
	/// ```
	#[must_use = "losing the pointer will leak memory"]
	pub fn into_parts_with_alloc(self) -> (NonNull<T>, usize, A) {
		todo!()
	}
	
	/// Returns a weak reference to the allocation. This does not count toward strong sharing, but
	/// guarantees that the underlying memory will not be deallocated.
	/// 
	/// Equivalent to [`Rc::downgrade`].
	/// 
	/// # Examples
	/// 
	/// ```
	/// use sharevec::array::vec::rc::ArrayVec;
	/// 
	/// let mut vec = ArrayVec::<_, 1>::new();
	/// let weak_vec = vec.demote();
	/// 
	/// assert_eq!(vec.try_push(1), Ok(()));
	/// ```
	pub fn demote(&self) -> Weak<T, N, A> {
		todo!()
	}
}

impl<T, const N: usize, A: Allocator> Unique<'_, T, N, A> {
	/// Consumes the reference, returning a weak reference to the allocation.
	/// 
	/// Equivalent to [`Rc::downgrade`].
	pub fn demote(self) -> Weak<T, N, A> {
		todo!()
	}
}

impl<T, const N: usize, A: Allocator> From<Rc<[T; N], A>> for ArrayVec<T, N, A> {
	fn from(value: Rc<[T; N], A>) -> Self {
		todo!()
	}
}

impl<T, const N: usize, A: Allocator> TryFrom<ArrayVec<T, N, A>> for Rc<[T; N], A> {
	type Error = ArrayVec<T, N, A>;

	fn try_from(value: ArrayVec<T, N, A>) -> Result<Self, Self::Error> {
		todo!()
	}
}

impl<T, const N: usize, A: Allocator> TryFrom<Rc<[T], A>> for ArrayVec<T, N, A> {
	type Error = Rc<[T], A>;

	fn try_from(value: Rc<[T], A>) -> Result<Self, Rc<[T], A>> {
		todo!()
	}
}

impl<const N: usize, A: Allocator> TryFrom<Rc<str, A>> for ArrayVec<u8, N, A> {
	type Error = Rc<str, A>;

	fn try_from(value: Rc<str, A>) -> Result<Self, Rc<str, A>> {
		todo!()
	}
}

impl<T, const N: usize, A: Allocator> From<ArrayVec<T, N, A>> for Rc<[T], A> {
	/// Note: the vector array is coerced into a slice, as it may not be full. If the full array is
	/// desired, a [`TryFrom`] implementation exists for this conversion.
	fn from(value: ArrayVec<T, N, A>) -> Self {
		todo!()
	}
}
