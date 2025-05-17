// Copyright 2024 - Strixpyrr
// SPDX-License-Identifier: Apache-2.0

//! # Internal Layout
//!
//! The layout of the inner allocation is exactly equivalent to `Rc<(usize, usize, [T; N])>`, four
//! `usize` words plus the array:
//!
//! ```text
//!  0        8       16       24       32..
//! |--------|--------|--------|--------|-------~
//! | strong |  weak  |  head  | length | array..
//! |--------|--------|--------|--------|-------~
//! ```

use alloc::{
	alloc::Global,
	boxed::Box,
	collections::VecDeque,
	string::String,
	vec::Vec as StdVec,
};
use core::alloc::{AllocError, Allocator};
use core::cmp::Ordering;
use core::fmt;
use core::hash::{Hash, Hasher};
use core::marker::PhantomData;
use core::ops::{Index, RangeBounds};
use core::ptr::NonNull;
use crate::array::{FullCapacity, TryExtend, TryExtendIter, TryFromSlice, TryInsert};
use crate::array::vec::ArrayVec;
use crate::error::{Result, Shared};
use crate::marker::RcVector;
use crate::vec::Vec;
pub(crate) use __private::ArrayDeque;
use drain::Drain;
use into_iter::IntoIter;
pub use iter::{Iter, IterMut};
use unique::Unique;
use weak::Weak;
use crate::deque::Deque;

#[cfg(target_has_atomic = "ptr")]
pub mod arc;
pub mod rc;

pub(crate) mod drain;
mod eq;
pub(crate) mod into_iter;
pub(crate) mod iter;
pub(crate) mod unique;
pub(crate) mod weak;

// Workaround for "struct is private" error
mod __private {
	use alloc::alloc::Global;
	use core::alloc::Allocator;
	use core::marker::PhantomData;
	use crate::raw::RawDeque;

	pub struct ArrayDeque<T, const N: usize, const ATOMIC: bool, A: Allocator = Global> {
		pub(crate) inner: RawDeque<[T; N], A>,
		pub(crate) head: usize,
		pub(crate) len: usize,
	}
}

impl<T, const N: usize, const ATOMIC: bool> ArrayDeque<T, N, ATOMIC> {
	/// Creates a new, empty deque with a fixed capacity.
	///
	/// # Panics
	///
	/// Panics if the capacity `N` is greater than [`isize::MAX`] minus four [`usize`] words, or if
	/// the allocator reports an allocation failure.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque: ArrayDeque<i32, 8> = ArrayDeque::new();
	/// ```
	#[must_use]
	pub fn new() -> Self {
		todo!()
	}

	/// Creates a new, empty deque with a fixed capacity.
	///
	/// # Errors
	///
	/// Returns an error if the allocator reports an allocation failure.
	///
	/// # Examples
	///
	/// ```
	/// #![feature(allocator_api)]
	/// 
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque: ArrayDeque<i32, 8> = ArrayDeque::try_new()?;
	/// # Ok::<_, core::alloc::AllocError>(())
	/// ```
	pub fn try_new() -> Result<Self, AllocError> {
		todo!()
	}
}

impl<T, const N: usize, A: Allocator, const ATOMIC: bool> ArrayDeque<T, N, ATOMIC, A> {
	/// The fixed capacity of the vector.
	pub const CAPACITY: usize = N;

	/// Creates a new, empty deque with a fixed capacity in the given allocator.
	///
	/// # Panics
	///
	/// Panics if the capacity `N` is greater than [`isize::MAX`] minus four [`usize`] words, or if
	/// the allocator reports an allocation failure.
	///
	/// # Examples
	///
	/// ```
	/// #![feature(allocator_api)]
	///
	/// # #[cfg(feature = "std")]
	/// # {
	/// use std::alloc::System;
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque: ArrayDeque<i32, 8, _> = ArrayDeque::new_in(System);
	/// # }
	/// ```
	#[must_use]
	pub fn new_in(alloc: A) -> Self {
		todo!()
	}

	/// Creates a new, empty deque with a fixed capacity in the given allocator.
	///
	/// # Errors
	///
	/// Returns an error if the allocator reports an allocation failure.
	///
	/// # Examples
	///
	/// ```
	/// #![feature(allocator_api)]
	///
	/// # #[cfg(feature = "std")]
	/// # {
	/// use std::alloc::System;
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque: ArrayDeque<i32, 8, _> = ArrayDeque::try_new_in(System)?;
	/// # }
	/// # Ok::<_, core::alloc::AllocError>(())
	/// ```
	pub fn try_new_in(alloc: A) -> Result<Self, AllocError> {
		todo!()
	}

	/// Returns the total number of elements the deque can hold.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque: ArrayDeque<i32, 8> = ArrayDeque::new();
	/// assert_eq!(deque.capacity(), 8);
	/// ```
	#[inline(always)]
	pub const fn capacity(&self) -> usize {
		Self::CAPACITY
	}

	/// Returns the number of elements the deque can hold before filled. This is shorthand for
	/// `N - length`.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque: ArrayDeque<i32, 8> = ArrayDeque::new();
	/// deque.extend([1, 2, 3]);
	///
	/// assert_eq!(deque.limit(), 5);
	///
	/// deque.extend([0; 5]);
	/// assert_eq!(deque.limit(), 0);
	/// ```
	pub const fn limit(&self) -> usize {
		todo!()
	}

	/// Returns a pair of slices over the contents of the deque.
	///
	/// If the deque is contiguous, all elements will be in the first slice and the second will be
	/// empty.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque: ArrayDeque<i32, 5> = ArrayDeque::new();
	/// _ = deque.push_back(0);
	/// _ = deque.push_back(1);
	/// _ = deque.push_back(2);
	///
	/// assert_eq!(deque.as_slices(), (&[0, 1, 2][..], &[][..]));
	///
	/// _ = deque.push_front(10);
	/// _ = deque.push_front(9);
	///
	/// assert_eq!(deque.as_slices(), (&[9, 10][..], &[0, 1, 2][..]));
	/// ```
	pub fn as_slices(&self) -> (&[T], &[T]) {
		todo!()
	}

	/// Returns a pair of mutable slices over the contents of the deque.
	///
	/// If the deque is contiguous, all elements will be in the first slice and the second will be
	/// empty.
	///
	/// # Errors
	///
	/// Returns an error if the vector holds a shared reference to its buffer.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque = ArrayDeque::<_, 4>::new();
	/// _ = deque.push_back(0);
	/// _ = deque.push_back(1);
	///
	/// _ = deque.push_front(10);
	/// _ = deque.push_front(9);
	///
	/// deque.try_as_mut_slices().unwrap().0[0] = 42;
	/// deque.try_as_mut_slices().unwrap().1[0] = 24;
	///
	/// assert_eq!(deque.as_slices(), (&[42, 10][..], &[24, 1][..]));
	/// ```
	pub fn try_as_mut_slices(&mut self) -> Result<(&mut [T], &mut [T])> {
		todo!()
	}

	/// Returns a raw pointer to the deque's buffer.
	///
	/// The caller must ensure that the deque outlives the pointer this function returns, or else
	/// it will end up dangling.
	///
	/// The caller must also ensure that the memory the pointer (non-transitively) points to is
	/// never written to (except inside an `UnsafeCell`) using this pointer or any pointer derived
	/// from it. If you need to mutate the contents of the slice, use [`as_mut_ptr`].
	///
	/// This method guarantees that for the purpose of the aliasing model, this method does not
	/// materialize a reference to the underlying slice, and thus the returned pointer will remain
	/// valid when mixed with other calls to [`as_ptr`], [`as_mut_ptr`], and [`as_non_null`]. Note
	/// that calling other methods that materialize mutable references to the slice, or mutable
	/// references to specific elements you are planning on accessing through this pointer, as well
	/// as writing to those elements, may still invalidate this pointer.
	///
	/// [`as_mut_ptr`]: Self::as_mut_ptr
	/// [`as_ptr`]: Self::as_ptr
	/// [`as_non_null`]: Self::as_non_null
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let deque: ArrayDeque<i32, 3> = ArrayDeque::from([1, 2, 4]);
	/// let ptr = deque.as_ptr();
	///
	/// unsafe {
	///     for i in 0..deque.len() {
	///         assert_eq!(*ptr.add(i), 1 << i);
	///     }
	/// }
	/// ```
	///
	/// Due to the aliasing guarantee, this code is valid:
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque: ArrayDeque<i32, 3> = ArrayDeque::from([1, 2, 3]);
	/// unsafe {
	///     let ptr1 = deque.as_ptr();
	///     assert_eq!(ptr1.read(), 1);
	///     let ptr2 = deque.as_mut_ptr().offset(2);
	///     ptr2.write(2);
	///     // Notably, writing to `ptr2` did *not* invalidate `ptr1`
	///     // because it mutated a different element:
	///     _ = ptr1.read();
	/// }
	/// ```
	pub fn as_ptr(&self) -> *const T {
		todo!()
	}
	/// Returns a raw pointer to the deque's buffer.
	///
	/// The caller must ensure that the deque outlives the pointer this function returns, or else
	/// it will end up dangling.
	///
	/// The caller must ensure that, for a [shared] buffer reference, the memory the pointer
	/// (non-transitively) points to is never written to (except inside an `UnsafeCell`) using this
	/// pointer or any pointer derived from it. The pointer must only be written to if the deque
	/// uniquely references its buffer.
	///
	/// This method guarantees that for the purpose of the aliasing model, this method does not
	/// materialize a reference to the underlying slice, and thus the returned pointer will remain
	/// valid when mixed with other calls to [`as_ptr`], [`as_mut_ptr`], and [`as_non_null`]. Note
	/// that calling other methods that materialize mutable references to the slice, or mutable
	/// references to specific elements you are planning on accessing through this pointer, as well
	/// as writing to those elements, may still invalidate this pointer.
	///
	/// [shared]: Self::is_shared
	/// [`as_mut_ptr`]: Self::as_mut_ptr
	/// [`as_ptr`]: Self::as_ptr
	/// [`as_non_null`]: Self::as_non_null
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque: ArrayDeque<i32, 8> = ArrayDeque::from([0; 8]);
	/// let ptr = deque.as_mut_ptr();
	///
	/// // Initialize elements via raw pointer writes.
	/// // This is safe because no other strong reference points to the vector contents.
	/// unsafe {
	///     for i in 0..deque.capacity() {
	///         ptr.add(i).write(i as i32);
	///     }
	/// }
	/// assert_eq!(deque, [1, 2, 3, 4, 5, 6, 7, 8]);
	/// ```
	///
	/// Due to the aliasing guarantee, this code is valid:
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque: ArrayDeque<i32, 1> = ArrayDeque::from([0]);
	/// unsafe {
	///     let ptr1 = deque.as_mut_ptr();
	///     ptr1.write(1);
	///     let ptr2 = deque.as_mut_ptr();
	///     ptr2.write(2);
	///     // Notably, writing to `ptr2` did *not* invalidate `ptr1`:
	///     ptr1.write(3);
	/// }
	/// ```
	pub fn as_mut_ptr(&mut self) -> *mut T {
		todo!()
	}
	/// Returns a `NonNull` pointer to the deque's buffer.
	///
	/// The caller must ensure that the deque outlives the pointer this function returns, or else
	/// will end up dangling.
	///
	/// The caller must ensure that, for a [shared] buffer reference, the memory the pointer
	/// (non-transitively) points to is never written to (except inside an `UnsafeCell`) using this
	/// pointer or any pointer derived from it. The pointer must only be written to if the deque
	/// uniquely references its buffer.
	///
	/// This method guarantees that for the purpose of the aliasing model, this method does not
	/// materialize a reference to the underlying slice, and thus the returned pointer will remain
	/// valid when mixed with other calls to [`as_ptr`], [`as_mut_ptr`], and [`as_non_null`]. Note
	/// that calling other methods that materialize mutable references to the slice, or mutable
	/// references to specific elements you are planning on accessing through this pointer, as well
	/// as writing to those elements, may still invalidate this pointer.
	///
	/// [shared]: Self::is_shared
	/// [`as_mut_ptr`]: Self::as_mut_ptr
	/// [`as_ptr`]: Self::as_ptr
	/// [`as_non_null`]: Self::as_non_null
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque: ArrayDeque<i32, 8> = ArrayDeque::from([0; 8]);
	/// let ptr = deque.as_non_null();
	///
	/// // Initialize elements via raw pointer writes.
	/// // This is safe because no other strong reference points to the vector contents.
	/// unsafe {
	///     for i in 0..deque.capacity() {
	///         ptr.add(i).write(i as i32);
	///     }
	/// }
	/// assert_eq!(deque, [1, 2, 3, 4, 5, 6, 7, 8]);
	/// ```
	///
	/// Due to the aliasing guarantee, this code is valid:
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque: ArrayDeque<i32, 1> = ArrayDeque::from([0]);
	/// unsafe {
	///     let ptr1 = deque.as_non_null();
	///     ptr1.write(1);
	///     let ptr2 = deque.as_non_null();
	///     ptr2.write(2);
	///     // Notably, writing to `ptr2` did *not* invalidate `ptr1`:
	///     ptr1.write(3);
	/// }
	/// ```
	pub fn as_non_null(&mut self) -> NonNull<T> {
		todo!()
	}

	/// Returns a reference to the underlying allocator.
	pub fn allocator(&self) -> &A {
		todo!()
	}

	/// Returns `true` if this deque holds the only strong reference to its allocated capacity,
	/// meaning no other deque shares it, allowing modification.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let deque: ArrayDeque<i32, 8> = ArrayDeque::new();
	/// let weak = deque.demote();
	/// assert!(deque.is_unique());
	/// ```
	pub fn is_unique(&self) -> bool {
		todo!()
	}
	/// Returns `true` if this deque does not hold the only reference to its allocated capacity,
	/// making it read-only. Only strong references count toward sharing.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let deque: ArrayDeque<i32, 8> = ArrayDeque::new();
	/// let clone = deque.clone();
	/// assert!(deque.is_shared());
	/// ```
	pub fn is_shared(&self) -> bool {
		!self.is_unique()
	}
	/// Returns `true` if this deque's allocated capacity is *not* weakly referenced.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let deque: ArrayDeque<i32, 8> = ArrayDeque::new();
	/// assert!(deque.is_weakly_unique());
	/// ```
	pub fn is_weakly_unique(&self) -> bool {
		self.weak_count() == 0
	}
	/// Returns `true` if this deque's allocated capacity is weakly referenced.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let deque: ArrayDeque<i32, 8> = ArrayDeque::new();
	/// let weak = deque.demote();
	/// assert!(deque.is_weakly_shared());
	/// ```
	pub fn is_weakly_shared(&self) -> bool {
		!self.is_weakly_unique()
	}

	/// Returns the number of strong references to the deque's allocated capacity.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let deque: ArrayDeque<i32, 8> = ArrayDeque::new();
	/// let clone = deque.clone();
	/// assert_eq!(deque.strong_count(), 2);
	/// ```
	pub fn strong_count(&self) -> usize {
		todo!()
	}
	/// Returns the number of weak references to the deque's allocated capacity.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let deque: ArrayDeque<i32, 8> = ArrayDeque::new();
	/// let weak = deque.demote();
	/// assert_eq!(deque.weak_count(), 1);
	/// ```
	pub fn weak_count(&self) -> usize {
		todo!()
	}
	/// If the deque is unique, returns a mutable view of the unique allocation.
	///
	/// Any weak references are disassociated from the contents without cloning. See the note on
	/// [`crate::array::vec::unique::Unique`] for details.
	///
	/// To clone out of a shared allocation into a unique one, use [`as_unique`] instead.
	///
	/// [`as_unique`]: Self::as_unique
	///
	/// # Errors
	///
	/// Returns an error if the vector holds a shared reference to its buffer.
	///
	/// # Panics
	///
	/// Panics if allocation fails, for example in an out-of-memory condition.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque: ArrayDeque<i32, 2> = ArrayDeque::new();
	///
	/// let mut unique = deque.unique().unwrap();
	/// assert_eq!(unique.push_front(1), Ok(()));
	/// assert_eq!(unique.push_front(2), Ok(()));
	/// assert_eq!(unique.push_front(3), Err(3));
	/// drop(unique);
	///
	/// let clone = deque.clone();
	/// assert!(deque.unique().is_err());
	/// drop(clone);
	///
	/// let weak = deque.demote();
	/// assert!(deque.unique().is_err());
	/// ```
	pub fn unique(&mut self) -> Result<Unique<T, N, A, ATOMIC>> {
		todo!()
	}

	/// Returns the number of elements in the deque.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let deque = ArrayDeque::from([1, 2, 3]);
	/// assert_eq!(deque.len(), 3);
	/// ```
	pub fn len(&self) -> usize {
		todo!()
	}
	/// Returns `true` if the deque contains no elements.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque: ArrayDeque<i32, 1> = ArrayDeque::new();
	/// assert!(!deque.is_not_empty());
	///
	/// _ = deque.push_back(1);
	/// assert!(deque.is_not_empty());
	/// ```
	pub fn is_empty(&self) -> bool {
		self.len() == 0
	}
	/// Returns `true` if the deque contains any elements.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque: ArrayDeque<i32, 1> = ArrayDeque::new();
	/// assert!(!deque.is_not_empty());
	///
	/// _ = deque.push_back(1);
	/// assert!(deque.is_not_empty());
	/// ```
	pub fn is_not_empty(&self) -> bool {
		!self.is_empty()
	}
	/// Returns `true` if the deque cannot hold any more elements.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque = ArrayDeque::from([1, 2, 3]);
	/// assert!(deque.is_full());
	///
	/// _ = deque.pop_back();
	/// assert!(!deque.is_full());
	/// ```
	pub fn is_full(&self) -> bool {
		self.len() == N
	}
	/// Returns `true` if the deque can hold more elements.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque = ArrayDeque::from([1, 2, 3]);
	/// assert!(!deque.is_not_full());
	///
	/// _ = deque.pop_back();
	/// assert!(deque.is_not_full());
	/// ```
	pub fn is_not_full(&self) -> bool {
		!self.is_full()
	}

	/// Returns a reference to the element at `index`, or `None` if the index is out of bounds.
	/// Index `0` is the front of the queue.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let deque = ArrayDeque::from([1, 2, 3]);
	/// assert_eq!(deque.get(1), Some(&2));
	/// assert_eq!(deque.get(3), None);
	/// ```
	pub fn get(&self, index: usize) -> Option<&T> {
		todo!()
	}
	/// Returns a reference to the front element, or `None` if the deque is empty.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque = ArrayDeque::from([1, 2, 3]);
	/// assert_eq!(deque.front(), Some(&1));
	/// deque.clear();
	/// assert_eq!(deque.front(), None);
	/// ```
	pub fn front(&self) -> Option<&T> {
		self.get(0)
	}
	/// Returns a reference to the back element, or `None` if the deque is empty.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque = ArrayDeque::from([1, 2, 3]);
	/// assert_eq!(deque.back(), Some(&3));
	/// deque.clear();
	/// assert_eq!(deque.back(), None);
	/// ```
	pub fn back(&self) -> Option<&T> {
		todo!()
	}
	/// Returns a mutable reference to the element at `index`, or `None` if the index is out of
	/// bounds. Index `0` is the front of the queue.
	///
	/// # Errors
	///
	/// Returns an error if the deque holds a shared reference to its buffer.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque = ArrayDeque::from([1, 2, 3]);
	///
	/// if let Ok(Some(v)) = deque.try_get_mut(1) {
	///     *v = 4;
	/// }
	/// assert_eq!(deque, [1, 4, 3]);
	/// ```
	pub fn try_get_mut(&mut self, index: usize) -> Result<Option<&mut T>> {
		todo!()
	}
	/// Returns a mutable reference to the front element, or `None` if the deque is empty.
	///
	/// # Errors
	///
	/// Returns an error if the deque holds a shared reference to its buffer.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque = ArrayDeque::from([1, 2, 3]);
	///
	/// if let Ok(Some(v)) = deque.try_front_mut() {
	///     *v = 4;
	/// }
	/// assert_eq!(deque, [4, 2, 3]);
	/// ```
	pub fn try_front_mut(&mut self) -> Result<Option<&mut T>> {
		self.try_get_mut(0)
	}
	/// Returns a mutable reference to the back element, or `None` if the deque is empty.
	///
	/// # Errors
	///
	/// Returns an error if the deque holds a shared reference to its buffer.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque = ArrayDeque::from([1, 2, 3]);
	///
	/// if let Ok(Some(v)) = deque.try_back_mut() {
	///     *v = 4;
	/// }
	/// assert_eq!(deque, [1, 2, 4]);
	/// ```
	pub fn try_back_mut(&mut self) -> Result<Option<&mut T>> {
		todo!()
	}

	/// Returns `true` if the deque contains an element equal to the given value.
	///
	/// This operation is *O*(*n*).
	///
	/// Note that if the deque is sorted, [`binary_search`] may be faster.
	///
	/// [`binary_search`]: Self::binary_search
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::arc::ArrayDeque;
	///
	/// let mut deque: ArrayDeque<i32, 2> = ArrayDeque::from([0, 1]);
	/// assert!(deque.contains(&1));
	/// assert!(!deque.contains(&10));
	/// ```
	pub fn contains(&self, value: &T) -> bool
	where
		T: PartialEq,
	{
		let (a, b) = self.as_slices();
		a.contains(value) || b.contains(value)
	}

	/// Shortens the deque, keeping the first `len` elements and dropping the rest. If `len` is
	/// greater or equal to the deque's current length, this has no effect.
	///
	/// # Leaking
	///
	/// Because memory may be shared and each shared deque may have a different length, truncation
	/// may cause elements outside `len` to go out of scope without dropping. The elements' [`Drop`]
	/// implementation can only be safely called when the deque holds a unique reference.
	///
	/// Rust does not require [`Drop::drop`] to be called, but this may be undesirable behavior for
	/// types with a non-trivial `drop` implementation. For such types, use [`unique`]/[`as_unique`]
	/// to get a mutable view which is guaranteed to drop elements, or [`is_unique`] to check for a
	/// unique reference.
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// struct WithDrop {
	///     val: i32
	/// }
	///
	/// impl Drop for WithDrop {
	///     fn drop(&mut self) {
	///        println!("Dropped {}", self.val);
	///     }
	/// }
	///
	/// let mut deque1 = ArrayDeque::from([
	///     WithDrop { val: 0 },
	///     WithDrop { val: 1 },
	///     WithDrop { val: 2 }
	/// ]);
	/// let mut deque2 = deque1.clone();
	///
	/// deque1.truncate(2);
	/// deque2.truncate(1);
	/// // The last element hasn't been dropped as would be expected, but it's become inaccessible
	/// assert_eq!(deque1.len(), 2);
	/// assert_eq!(deque2.len(), 1);
	///
	/// // Now only the first element is accessible. None of them have been dropped.
	/// drop(deque1);
	/// assert_eq!(deque2[0].val, 0);
	/// assert!(deque2.get(1).is_none());
	///
	/// // The second and third elements could be overwritten without dropping!
	/// deque2.try_push_back(WithDrop { val: 3 }).unwrap();
	/// deque2.try_push_back(WithDrop { val: 4 }).unwrap();
	/// // Output:
	/// // Dropping 3
	/// // Dropping 4
	/// deque2.truncate(1);
	/// ```
	///
	/// [`unique`]: Self::unique
	/// [`as_unique`]: Self::as_unique
	/// [`is_unique`]: Self::is_unique
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque: ArrayDeque<i32, 5> = ArrayDeque::from([1, 2, 3, 4, 5]);
	/// // Truncates from 5 elements to 2
	/// deque.truncate(2);
	/// assert_eq!(deque, [1, 2]);
	/// // No truncation occurs when the length is greater than the deque's current length
	/// deque.truncate(8);
	/// assert_eq!(deque, [1, 2]);
	/// // Truncating to 0 elements is equivalent to `clear`
	/// deque.truncate(0);
	/// assert_eq!(deque, []);
	/// ```
	pub fn truncate(&mut self, len: usize) {
		todo!()
	}

	/// Returns an iterator returning references to elements front-to-back.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let deque: ArrayDeque<i32, 3> = ArrayDeque::from([1, 2, 3]);
	///
	/// assert!(deque.iter().eq(&[1, 2, 3]))
	/// ```
	pub fn iter(&self) -> Iter<T> {
		let (a, b) = self.as_slices();
		Iter::new(a.iter(), b.iter())
	}
	/// Returns an iterator returning mutable references to elements front-to-back.
	///
	/// # Errors
	///
	/// Returns an error if the deque holds a shared reference to its buffer.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque: ArrayDeque<i32, 3> = ArrayDeque::from([1, 2, 3]);
	///
	/// for v in deque.try_iter_mut().unwrap() {
	///     *v *= 2;
	/// }
	///
	/// assert_eq!(deque, [2, 4, 6]);
	/// ```
	pub fn try_iter_mut(&mut self) -> Result<IterMut<T>> {
		let (a, b) = self.try_as_mut_slices()?;
		Ok(IterMut::new(a.iter_mut(), b.iter_mut()))
	}

	/// Returns an iterator returning references to elements within a range.
	///
	/// # Panics
	///
	/// Panics if the starting point is greater than the end point or if the end point is greater
	/// than the length of the deque.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let deque = ArrayDeque::from([1, 2, 3]);
	/// let range = deque.range(2..).copied().collect::<ArrayDeque<_, 1>>();
	/// assert_eq!(range, [3]);
	/// ```
	pub fn range<R: RangeBounds<usize>>(&self, range: R) -> Iter<T> {
		todo!()
	}
	/// Returns an iterator returning mutable references to elements within a range.
	///
	/// # Panics
	///
	/// Panics if the starting point is greater than the end point or if the end point is greater
	/// than the length of the deque.
	///
	/// # Errors
	///
	/// Returns an error if the deque holds a shared reference to its buffer.
	///
	/// # Examples
	///
	/// ```
	/// # use sharevec::error::Shared;
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque = ArrayDeque::from([1, 2, 3]);
	/// for v in deque.try_range_mut(2..)? {
	///     *v *= 2;
	/// }
	/// assert_eq!(deque, [1, 2, 6]);
	/// # Ok::<_, Shared>(())
	/// ```
	pub fn try_range_mut<R: RangeBounds<usize>>(&mut self, range: R) -> Result<IterMut<T>> {
		todo!()
	}

	/// Removes the first element and returns it, or `None` if the deque is empty.
	///
	/// # Errors
	///
	/// Returns an error if the deque holds a shared reference to its buffer.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque = ArrayDeque::from([1, 2]);
	/// assert_eq!(deque.try_pop_front(), Ok(Some(1)));
	/// assert_eq!(deque.try_pop_front(), Ok(Some(2)));
	/// assert_eq!(deque.try_pop_front(), Ok(None));
	/// ```
	pub fn try_pop_front(&mut self) -> Result<Option<T>> {
		todo!()
	}
	/// Removes the last element and returns it, or `None` if the deque is empty.
	///
	/// # Errors
	///
	/// Returns an error if the deque holds a shared reference to its buffer.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque = ArrayDeque::from([1, 2]);
	/// assert_eq!(deque.try_pop_back(), Ok(Some(2)));
	/// assert_eq!(deque.try_pop_back(), Ok(Some(1)));
	/// assert_eq!(deque.try_pop_back(), Ok(None));
	/// ```
	pub fn try_pop_back(&mut self) -> Result<Option<T>> {
		todo!()
	}
	/// Prepends an element to the deque.
	///
	/// # Errors
	///
	/// Returns [`TryInsert::Shared`] if the deque holds a shared reference to its buffer, or
	/// [`TryInsert::FullCapacity`] is the deque is full.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque = ArrayDeque::<_, 2>::new();
	/// assert_eq!(deque.try_push_front(1), Ok(()));
	/// assert_eq!(deque.try_push_front(2), Ok(()));
	/// assert_eq!(deque.try_push_front(3).map_err(|e| e.element()), &Err(3));
	/// assert_eq!(deque, [2, 1]);
	/// ```
	pub fn try_push_front(&mut self, value: T) -> Result<(), TryInsert<T>> {
		todo!()
	}
	/// Appends an element to the back of the deque.
	///
	/// # Errors
	///
	/// Returns [`TryInsert::Shared`] if the deque holds a shared reference to its buffer, or
	/// [`TryInsert::FullCapacity`] is the deque is full.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque = ArrayDeque::<_, 2>::new();
	/// assert_eq!(deque.try_push_back(1), Ok(()));
	/// assert_eq!(deque.try_push_back(2), Ok(()));
	/// assert_eq!(deque.try_push_back(3).map_err(|e| e.element()), &Err(3));
	/// assert_eq!(deque, [1, 2]);
	/// ```
	pub fn try_push_back(&mut self, value: T) -> Result<(), TryInsert<T>> {
		todo!()
	}

	/// Swaps elements at indices `i` and `j`, where index `0` is the front of the queue. Both may
	/// be equal.
	///
	/// # Panics
	///
	/// Panics if either index is out of bounds.
	///
	/// # Errors
	///
	/// Returns an error if the deque holds a shared reference to its buffer.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut buf = ArrayDeque::from([1, 2, 3]);
	/// assert_eq!(buf, [1, 2, 3]);
	/// assert_eq!(buf.try_swap(0, 2), Ok(()));
	/// assert_eq!(buf, [3, 2, 1]);
	/// ```
	pub fn try_swap(&mut self, i: usize, j: usize) -> Result {
		todo!()
	}

	/// Removes and returns the element at `index` from the deque, replacing it with the first
	/// element. Index `0` is at the front of the queue.
	///
	/// This does not preserve ordering, but is *O*(1). If ordering must be preserved, use
	/// [`try_remove`].
	///
	/// Returns `None` if `index` is out of bounds.
	///
	/// [`try_remove`]: Self::try_remove
	///
	/// # Errors
	///
	/// Returns an error if the deque holds a shared reference to its buffer.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque = ArrayDeque::from([1, 2, 3]);
	/// assert_eq!(deque.try_swap_remove_front(2), Ok(Some(3)));
	/// assert_eq!(deque, [2, 1]);
	/// deque.clear();
	/// assert_eq!(deque.try_swap_remove_front(0), Ok(None));
	/// ```
	pub fn try_swap_remove_front(&mut self, index: usize) -> Result<Option<T>> {
		todo!()
	}
	/// Removes and returns the element at `index` from the deque, replacing it with the last
	/// element. Index `0` is at the front of the queue.
	///
	/// This does not preserve ordering, but is *O*(1). If ordering must be preserved, use
	/// [`try_remove`].
	///
	/// Returns `None` if `index` is out of bounds.
	///
	/// [`try_remove`]: Self::try_remove
	///
	/// # Errors
	///
	/// Returns an error if the deque holds a shared reference to its buffer.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque = ArrayDeque::from([1, 2, 3]);
	/// assert_eq!(deque.try_swap_remove_back(0), Ok(Some(1)));
	/// assert_eq!(deque, [3, 2]);
	/// deque.clear();
	/// assert_eq!(deque.try_swap_remove_back(0), Ok(None));
	/// ```
	pub fn try_swap_remove_back(&mut self, index: usize) -> Result<Option<T>> {
		todo!()
	}

	/// Removes and returns the element at `index` from the deque, shifting subsequent elements at
	/// whichever end is closer to the removal point. Index `0` is at the front of the queue.
	///
	/// Returns `None` if `index` is out of bounds.
	///
	/// # Errors
	///
	/// Returns an error if the deque is immutable because it holds a shared reference to its
	/// buffer.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque = ArrayDeque::from([1, 2, 3]);
	/// assert_eq!(deque.try_remove(1), Ok(Some(2)));
	/// assert_eq!(deque, [1, 3]);
	/// ```
	pub fn try_remove(&mut self, index: usize) -> Result<Option<T>> {
		todo!()
	}

	/// Inserts an element at position `index` within the deque, shifting subsequent elements toward
	/// the back. Index `0` is at the front of the queue.
	///
	/// # Errors
	///
	/// Returns [`TryInsert::Shared`] if the deque has free capacity, but is immutable because it
	/// holds a shared reference to its buffer. If the deque is full, [`TryInsert::FullCapacity`]
	/// is returned and the deque is not modified.
	///
	/// # Panics
	///
	/// Panics if `index` is greater than the deque length.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque = ArrayDeque::<_, 4>::new();
	/// assert_eq!(deque.try_push_back(1), Ok(()));
	/// assert_eq!(deque.try_push_back(3), Ok(()));
	/// assert_eq!(deque.try_push_back(4), Ok(()));
	/// assert_eq!(deque, [1, 3, 4]);
	///
	/// assert_eq!(deque.try_insert(1, 2), Ok(()));
	/// assert_eq!(deque, [1, 2, 3, 4]);
	/// ```
	pub fn try_insert(&mut self, index: usize, element: T) -> Result<(), TryInsert<T>> {
		todo!()
	}

	/// Retains the elements specified by `predicate`, dropping the rest.
	///
	/// Removes all elements `e` for which `predicate(&e)` returns `false`. This method operates
	/// in-place, visiting each element exactly once in the original order, and preserves the order
	/// of the retained elements.
	///
	/// # Errors
	///
	/// Returns an error if the deque is immutable because it holds a shared reference to its
	/// buffer.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque: ArrayDeque<i32, 4> = ArrayDeque::from([1, 2, 3, 4]);
	/// assert_eq!(deque.try_retain(|&x| x % 2 == 0), Ok(()));
	/// assert_eq!(deque, [2, 4]);
	/// ```
	pub fn try_retain<F: FnMut(&T) -> bool>(&mut self, predicate: F) -> Result {
		todo!()
	}
	/// Retains the elements specified by `predicate`, dropping the rest.
	///
	/// Removes all elements `e` for which `predicate(&mut e)` returns `false`. This method operates
	/// in-place, visiting each element exactly once in the original order, and preserves the order
	/// of the retained elements.
	///
	/// # Errors
	///
	/// Returns an error if the deque is immutable because it holds a shared reference to its
	/// buffer.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque: ArrayDeque<i32, 4> = ArrayDeque::from([1, 2, 3, 4]);
	/// assert_eq!(
	///     deque.try_retain_mut(|x| if *x % 2 == 0 {
	///         *x += 1;
	///         true
	///     } else {
	///         false
	///     }),
	///     Ok(())
	/// );
	/// assert_eq!(deque, [3, 5]);
	/// ```
	pub fn try_retain_mut<F: FnMut(&mut T) -> bool>(&mut self, predicate: F) -> Result {
		todo!()
	}

	/// Moves all elements from `other` into this deque, leaving `other` empty. Any atomic vector
	/// type from this crate may be appended, even array vectors/deques with a different fixed
	/// capacity.
	///
	/// # Errors
	///
	/// Returns [`Shared`] if either of the vectors/deques are immutable because they hold a shared
	/// reference to their respective buffers. Returns [`FullCapacity`] if the deque would overflow
	/// its fixed capacity after appending `other`. In either case, neither vector/deque is modified.
	/// 
	/// [`Shared`]: TryExtend::Shared
	/// [`FullCapacity`]: TryExtend::FullCapacity
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::TryExtend;
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque1: ArrayDeque<i32, 7> = ArrayDeque::new();
	/// deque1.extend([1, 2, 3]);
	/// let mut deque2 = ArrayDeque::from([4, 5, 6]);
	/// let mut deque3 = ArrayDeque::from([7, 8, 9]);
	/// assert_eq!(deque1.try_append(&mut deque2), Ok(()));
	/// assert_eq!(deque1, [1, 2, 3, 4, 5, 6]);
	/// assert_eq!(deque2, []);
	///
	/// assert_eq!(deque2.try_append(&mut deque3), Err(TryExtend::FullCapacity { remaining: 2 }));
	/// assert_eq!(deque1, [1, 2, 3, 4, 5, 6, 7]);
	/// assert_eq!(deque3, [8, 9]);
	/// ```
	pub fn try_append<V: RcVector<T, A, ATOMIC> + ?Sized>(&mut self, other: &mut V) -> Result<(), TryExtend> {
		todo!()
	}

	/// Removes the specified range from the deque, returning all removed elements as an iterator.
	/// If the iterator is dropped before being fully consumed, the remaining removed elements are
	/// dropped.
	///
	/// # Panics
	///
	/// Panics if the starting point is greater than the end point or if the end point is greater
	/// than the length of the deque.
	///
	/// # Errors
	///
	/// Returns an error if the deque is immutable because it holds a shared reference to its
	/// buffer.
	///
	/// # Leaking
	///
	/// If the returned iterator goes out of scope without being dropped (due to [`forget`], for
	/// example), the deque may have lost and leaked elements arbitrarily, including elements
	/// outside the range.
	///
	/// [`forget`]: core::mem::forget
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque: ArrayDeque<i32, 8> = ArrayDeque::from([1, 2, 3, 4, 5, 6, 7, 8]);
	/// let removed = deque.try_drain(2..6).map(Iterator::collect::<ArrayDeque<_, 4>>);
	/// assert_eq!(removed, Ok([3, 4, 5, 6].into()));
	/// assert_eq!(deque, [1, 2, 7, 8]);
	/// ```
	pub fn try_drain<R: RangeBounds<usize>>(&mut self, range: R) -> Result<Drain<T, N, A, ATOMIC>> {
		todo!()
	}

	/// Clears the deque, removing all values.
	///
	/// # Leaking
	///
	/// Because memory may be shared and each shared deque may have a different length, clearing may
	/// cause all elements to go out of scope without dropping. The elements' [`Drop`]
	/// implementation can only be safely called when the deque holds a unique reference.
	///
	/// Rust does not require [`Drop::drop`] to be called, but this may be undesirable behavior for
	/// types with a non-trivial `drop` implementation. For such types, use [`unique`]/[`as_unique`]
	/// to get a mutable view which is guaranteed to drop elements, or [`is_unique`] to check for a
	/// unique reference.
	///
	/// ```
	/// # use sharevec::array::TryInsert;
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// struct WithDrop {
	///     val: i32
	/// }
	///
	/// impl Drop for WithDrop {
	///     fn drop(&mut self) {
	///        println!("Dropped {}", self.val);
	///     }
	/// }
	///
	/// let mut deque1 = ArrayDeque::from([
	///     WithDrop { val: 0 },
	///     WithDrop { val: 1 },
	///     WithDrop { val: 2 }
	/// ]);
	/// let mut deque2 = deque1.clone();
	///
	/// deque1.clear();
	/// deque2.clear();
	/// // The elements haven't been dropped as would be expected, but they've become inaccessible
	/// assert!(deque1.is_empty());
	/// assert!(deque2.is_empty());
	/// drop(deque2);
	///
	/// // Any of the elements could be overwritten without dropping!
	/// deque1.try_push_back(WithDrop { val: 3 })?;
	/// // Output:
	/// // Dropping 3
	/// deque1.clear();
	/// # Ok::<_, TryInsert<WithDrop>>(())
	/// ```
	///
	/// [`unique`]: Self::unique
	/// [`as_unique`]: Self::as_unique
	/// [`is_unique`]: Self::is_unique
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque: ArrayDeque<i32, 3> = ArrayDeque::from([1, 2, 3]);
	/// deque.clear();
	///
	/// assert_eq!(deque, []);
	/// ```
	pub fn clear(&mut self) {
		todo!()
	}

	/// Splits the deque into two at the given index.
	///
	/// Returns a new deque containing the elements starting from the given index. The original is
	/// left containing the elements up to `at` (exclusive).
	///
	/// - If you want to take ownership of the entire contents and capacity of the deque, use
	///   [`mem::take`] or [`mem::replace`].
	/// - If you don't need the returned deque at all, see [`truncate`].
	/// - If you want to take ownership of an arbitrary range, or you don't necessarily want to
	///   store the removed items, see [`try_drain`].
	///
	/// [`mem::take`]: core::mem::take
	/// [`mem::replace`]: core::mem::replace
	/// [`truncate`]: Self::truncate
	/// [`try_drain`]: Self::try_drain
	///
	/// # Panics
	///
	/// Panics if `at` is greater than the deque length.
	///
	/// # Errors
	///
	/// Returns an error if the deque is immutable because it holds a shared reference to its
	/// buffer.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque = ArrayDeque::from([1, 2, 3, 4]);
	/// assert!(deque.try_split_off(2).is_ok_and(|d| d == [3, 4]));
	/// assert_eq!(deque, [1, 2]);
	/// ```
	pub fn try_split_off(&mut self, at: usize) -> Result<Self> where A: Clone {
		todo!()
	}

	/// Resizes the deque in-place to the specified length.
	///
	/// If `new_len` is greater than the current length, the deque is extended, filling the
	/// additional space with element returned from calling the closure `fill`. If `new_len` is less
	/// than the current length, the deque is truncated.
	///
	/// To fill the additional space by [`Clone`]ing a given value, use [`try_resize`]. To fill with
	/// default values, pass [`Default::default`] as the second argument.
	///
	/// [`try_resize`]: Self::try_resize
	///
	/// # Leaking
	///
	/// If the deque is truncated, the same leaking caveats as [`truncate`] apply.
	///
	/// [`truncate`]: Self::truncate#leaking
	///
	/// # Errors
	///
	/// Returns [`Shared`] if the deque is immutable because it holds a shared reference to its
	/// buffer. Returns [`FullCapacity`] if the new length would be larger than the fixed capacity
	/// of the deque. In this case, the deque is filled completely.
	/// 
	/// [`Shared`]: TryExtend::Shared
	/// [`FullCapacity`]: TryExtend::FullCapacity
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::TryExtend;
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque: ArrayDeque<i32, 8> = ArrayDeque::new();
	/// deque.try_extend([1, 2, 3]).unwrap();
	/// let fill = Default::default;
	///
	/// assert_eq!(deque.try_resize_with(5, fill), Ok(()));
	/// assert_eq!(deque, [1, 2, 3, 0, 0]);
	/// assert_eq!(deque.try_resize_with(3, fill), Ok(()));
	/// assert_eq!(deque, [1, 2, 3]);
	/// assert_eq!(deque.try_resize_with(16, fill), Err(TryExtend::FullCapacity { remaining: 8 }));
	/// assert_eq!(deque, [1, 2, 3, 0, 0, 0, 0, 0]);
	/// ```
	pub fn try_resize_with<F: FnMut() -> T>(&mut self, new_len: usize, fill: F) -> Result<(), TryExtend> {
		todo!()
	}

	/// Rearranges the contents of the deque such that they are stored in a single contiguous slice,
	/// returning the slice. The order of the elements in the deque is preserved; only the internal
	/// storage is changed.
	///
	/// Once the internal storage is contiguous, the [`as_slices`] and [`try_as_mut_slices`] will
	/// return the entire contents of the deque in a single slice. If this operation succeeds, the
	/// deque is always unique until cloned.
	///
	/// [`as_slices`]: Self::as_slices
	/// [`try_as_mut_slices`]: Self::try_as_mut_slices
	///
	/// # Errors
	///
	/// Returns an error if the deque holds a shared reference to its buffer.
	///
	/// # Examples
	/// 
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque: ArrayDeque<i32, 3> = ArrayDeque::new();
	///
	/// _ = deque.push_back(2);
	/// _ = deque.push_back(1);
	/// _ = deque.push_front(3);
	/// assert_eq!(deque.as_slices(), (&[2, 1][..], &[3][..]));
	///
	/// _ = deque.try_make_contiguous();
	/// assert_eq!(deque.as_slices(), (&[3, 2, 1][..], &[][..]));
	/// ```
	pub fn try_make_contiguous(&mut self) -> Result<&mut [T]> {
		todo!()
	}

	/// Rotates the deque contents `n` places to the left, such that the element at index `n` is the
	/// first element. This is equivalent to rotating right by `len() - n`.
	///
	/// # Panics
	///
	/// Panics if `n` is greater than the length of the deque. When `n` is equal to the length, this
	/// operation simply does nothing *without* panicking.
	///
	/// # Errors
	///
	/// Returns an error if the deque holds a shared reference to its buffer.
	///
	/// # Time complexity
	///
	/// Takes *O*(`min(n, len() - n)`) time.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque: ArrayDeque<i32, 10> = (0..10).collect();
	///
	/// assert_eq!(deque.try_rotate_left(3), Ok(()));
	/// assert_eq!(deque, [3, 4, 5, 6, 7, 8, 9, 0, 1, 2]);
	///
	/// for i in 1..10 {
	///     assert_eq!(i * 3 % 10, deque[0]);
	///     assert_eq!(deque.try_rotate_left(3), Ok(()));
	/// }
	/// assert_eq!(deque, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]);
	/// ```
	pub fn try_rotate_left(&mut self, n: usize) -> Result {
		todo!()
	}
	/// Rotates the deque contents `n` places to the right, such that the first element is at index
	/// `n`. This is equivalent to rotating left by `len() - n`.
	///
	/// # Panics
	///
	/// Panics if `n` is greater than the length of the deque. When `n` is equal to the length, this
	/// operation simply does nothing *without* panicking.
	///
	/// # Errors
	///
	/// Returns an error if the deque holds a shared reference to its buffer.
	///
	/// # Time complexity
	///
	/// Takes *O*(`min(n, len() - n)`) time.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque: ArrayDeque<i32, 10> = (0..10).collect();
	///
	/// assert_eq!(deque.try_rotate_right(3), Ok(()));
	/// assert_eq!(deque, [7, 8, 9, 0, 1, 2, 3, 4, 5, 6]);
	///
	/// for i in 1..10 {
	///     assert_eq!(0, deque[i * 3 % 10]);
	///     assert_eq!(deque.try_rotate_right(3), Ok(()));
	/// }
	/// assert_eq!(deque, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]);
	/// ```
	pub fn try_rotate_right(&mut self, n: usize) -> Result {
		todo!()
	}

	/// Binary searches the deque for the specified element. If the deque is not sorted, the result
	/// is unspecified and meaningless.
	///
	/// [`Ok`] is returned if the element is found, containing the index of the matching element. If
	/// multiple matches are found, any one of their indices may be returned. [`Err`] is returned if
	/// the element is not found, containing the index where a matching element could be inserted
	/// while maintaining the sorted order.
	///
	/// See also [`binary_search_by`], [`binary_search_by_key`], and [`partition_point`].
	///
	/// [`binary_search_by`]: Self::binary_search_by
	/// [`binary_search_by_key`]: Self::binary_search_by_key
	/// [`partition_point`]: Self::partition_point
	///
	/// # Examples
	///
	/// Looks up a series of four elements. The first is found, with a uniquely determined position;
	/// the second and third are not found; the fourth could match any position in `[1, 4]`.
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let deque = ArrayDeque::from([0, 1, 1, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55]);
	///
	/// assert_eq!(deque.binary_search(&13),  Ok(9));
	/// assert_eq!(deque.binary_search(&4),   Err(7));
	/// assert_eq!(deque.binary_search(&100), Err(13));
	/// let r = deque.binary_search(&1);
	/// assert!(matches!(r, Ok(1..=4)));
	/// ```
	///
	/// If you want to insert an item to a sorted deque, while maintaining sort order, consider
	/// using [`partition_point`]:
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque = ArrayDeque::from([0, 1, 1, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55]);
	/// let num = 42;
	/// let idx = deque.partition_point(|&x| x <= num);
	/// // If `num` is unique, `s.partition_point(|&x| x < num)` (with `<`) is equivalent to
	/// // `s.binary_search(&num).unwrap_or_else(|x| x)`, but using `<=` may allow `insert`
	/// // to shift less elements.
	/// assert_eq!(deque.try_insert(idx, num), Ok(()));
	/// assert_eq!(deque, [0, 1, 1, 1, 1, 2, 3, 5, 8, 13, 21, 34, 42, 55]);
	/// ```
	#[allow(clippy::missing_errors_doc)]
	pub fn binary_search(&self, x: &T) -> Result<usize, usize>
	where
		T: Ord,
	{
		self.binary_search_by(|e| e.cmp(x))
	}
	/// Binary searches the deque with a comparator function.
	///
	/// The comparator function returns an [ordering](Ordering) indicating whether its argument is
	/// less than, equal to, or greater than the desired target. If the deque is not sorted or the
	/// comparator function does not return an order consistent with the sort order of the deque,
	/// the result is unspecified and meaningless.
	///
	/// [`Ok`] is returned if the element is found, containing the index of the matching element. If
	/// multiple matches are found, any one of their indices may be returned. [`Err`] is returned if
	/// the element is not found, containing the index where a matching element could be inserted
	/// while maintaining the sorted order.
	///
	/// See also [`binary_search`], [`binary_search_by_key`], and [`partition_point`].
	///
	/// [`binary_search`]: Self::binary_search
	/// [`binary_search_by_key`]: Self::binary_search_by_key
	/// [`partition_point`]: Self::partition_point
	///
	/// # Examples
	///
	/// Looks up a series of four elements. The first is found, with a uniquely determined position;
	/// the second and third are not found; the fourth could match any position in `[1, 4]`.
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let deque = ArrayDeque::from([0, 1, 1, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55]);
	///
	/// assert_eq!(deque.binary_search_by(|x| x.cmp(&13)),  Ok(9));
	/// assert_eq!(deque.binary_search_by(|x| x.cmp(&4)),   Err(7));
	/// assert_eq!(deque.binary_search_by(|x| x.cmp(&100)), Err(13));
	/// let r = deque.binary_search_by(|x| x.cmp(&1));
	/// assert!(matches!(r, Ok(1..=4)));
	/// ```
	#[allow(clippy::missing_errors_doc)]
	pub fn binary_search_by<F>(&self, mut compare: F) -> Result<usize, usize>
	where
		F: FnMut(&T) -> Ordering,
	{
		todo!()
	}
	/// Binary searches this deque with a key mapping function. If the deque is not sorted by the
	/// key, the result is unspecified and meaningless.
	///
	/// [`Ok`] is returned if the element is found, containing the index of the matching element. If
	/// multiple matches are found, any one of their indices may be returned. [`Err`] is returned if
	/// the element is not found, containing the index where a matching element could be inserted
	/// while maintaining the sorted order.
	///
	/// See also [`binary_search`], [`binary_search_by`], and [`partition_point`].
	///
	/// [`binary_search`]: Self::binary_search
	/// [`binary_search_by`]: Self::binary_search_by
	/// [`partition_point`]: Self::partition_point
	///
	/// # Examples
	///
	/// Looks up a series of four elements in a slice of pairs sorted by their second elements. The
	/// first is found, with a uniquely determined position; the second and third are not found; the
	/// fourth could match any position in `[1, 4]`.
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let deque = ArrayDeque::from([
	///     (0, 0), (2, 1), (4, 1), (5, 1), (3, 1),
	///     (1, 2), (2, 3), (4, 5), (5, 8), (3, 13),
	///     (1, 21), (2, 34), (4, 55)
	/// ]);
	///
	/// assert_eq!(deque.binary_search_by_key(&13, |&(a, b)| b),  Ok(9));
	/// assert_eq!(deque.binary_search_by_key(&4, |&(a, b)| b),   Err(7));
	/// assert_eq!(deque.binary_search_by_key(&100, |&(a, b)| b), Err(13));
	/// let r = deque.binary_search_by_key(&1, |&(a, b)| b);
	/// assert!(matches!(r, Ok(1..=4)));
	/// ```
	#[allow(clippy::missing_errors_doc)]
	pub fn binary_search_by_key<B, F>(&self, key: &B, mut map: F) -> Result<usize, usize>
	where
		F: FnMut(&T) -> B,
		B: Ord,
	{
		self.binary_search_by(|k| map(k).cmp(key))
	}

	/// Returns the index of the partition point according to the given predicate (the index of the
	/// first element of the second partition).
	///
	/// The deque is assumed to be partitioned according to the given predicate. This means that all
	/// elements for which the predicate returns `true` must be at the start of the deque, and all
	/// elements for which the predicate returns `false` must be at the end. For example,
	/// `[7, 15, 3, 5, 4, 12, 6]` is partitioned under the predicate `x % 2 != 0` (all odd numbers
	/// are at the start, all even at the end).
	///
	/// If the deque is not partitioned, the result is unspecified and meaningless, as this method
	/// performs a kind of binary search.
	///
	/// See also [`binary_search`], [`binary_search_by`], and [`binary_search_by_key`].
	///
	/// [`binary_search`]: Self::binary_search
	/// [`binary_search_by`]: Self::binary_search_by
	/// [`binary_search_by_key`]: Self::binary_search_by_key
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let deque = ArrayDeque::from([1, 2, 3, 3, 5, 6, 7]);
	/// let i = deque.partition_point(|&x| x < 5);
	///
	/// assert_eq!(i, 4);
	/// assert!(deque.iter().take(i).all(|&x| x < 5));
	/// assert!(deque.iter().skip(i).all(|&x| !(x < 5)));
	/// ```
	///
	/// If you want to insert an item to a sorted deque, while maintaining
	/// sort order:
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque = ArrayDeque::from([0, 1, 1, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55]);
	/// let num = 42;
	/// let idx = deque.partition_point(|&x| x < num);
	/// assert_eq!(deque.try_insert(idx, num), Ok(()));
	/// assert_eq!(deque, [0, 1, 1, 1, 1, 2, 3, 5, 8, 13, 21, 34, 42, 55]);
	/// ```
	pub fn partition_point<P>(&self, mut pred: P) -> usize
	where
		P: FnMut(&T) -> bool,
	{
		todo!()
	}

	/// Mutably indexes the deque, if it holds a unique reference.
	///
	/// To use the `deque[index]` syntax, use [`unique`]/[`as_unique`] to get a [`Unique`] wrapper.
	///
	/// [`unique`]: Self::unique
	/// [`as_unique`]: Self::as_unique
	///
	/// # Errors
	///
	/// Returns an error if the deque is immutable because it holds a shared reference to its
	/// buffer.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque: ArrayDeque<i32, 3> = ArrayDeque::from([1, 2, 3]);
	///
	/// for i in 0..deque.len() {
	///     *deque.try_index_mut(i).unwrap() = i as i32 * 2;
	/// }
	/// assert_eq!(deque, [2, 4, 6]);
	///
	/// // `deque.try_index_mut(4)` would panic
	/// ```
	pub fn try_index_mut(&mut self, index: usize) -> Result<&mut T> {
		todo!()
	}
	
	/// Appends elements from an iterator to the back of the deque.
	///
	/// # Errors
	///
	/// Returns [`FullCapacity`] if the deque is filled before the full iterator could be appended.
	/// In this case, the deque is filled completely and the error contains the number of elements
	/// remaining and the partially consumed iterator. [`Shared`] is returned if the deque is
	/// immutable because it holds a shared reference to its buffer.
	/// 
	/// [`FullCapacity`]: TryExtendIter::FullCapacity
	/// [`Shared`]: TryExtendIter::Shared
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque: ArrayDeque<i32, 3> = ArrayDeque::new();
	/// assert_eq!(deque.try_extend([1, 2]), Ok(()));
	/// assert_eq!(deque, [1, 2]);
	/// assert!(deque.try_extend([3, 4, 5]).is_err());
	/// assert_eq!(deque, [1, 2, 3]);
	/// ```
	pub fn try_extend<I: IntoIterator<Item = T>>(&mut self, iter: I) -> Result<(), TryExtendIter<I>> {
		todo!()
	}
	/// Appends referenced elements from an iterator to the back of the deque by copying.
	///
	/// # Errors
	///
	/// Returns [`FullCapacity`] if the deque is filled before the full iterator could be appended.
	/// In this case, the deque is filled completely and the error contains the number of elements
	/// remaining and the partially consumed iterator. [`Shared`] is returned if the deque is
	/// immutable because it holds a shared reference to its buffer.
	/// 
	/// [`FullCapacity`]: TryExtendIter::FullCapacity
	/// [`Shared`]: TryExtendIter::Shared
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque: ArrayDeque<i32, 3> = ArrayDeque::new();
	/// assert_eq!(deque.try_extend_ref(&[1, 2]), Ok(()));
	/// assert_eq!(deque, [1, 2]);
	/// assert!(deque.try_extend_ref(&[3, 4, 5]).is_err());
	/// assert_eq!(deque, [1, 2, 3]);
	/// ```
	pub fn try_extend_ref<'a, I: IntoIterator<Item = &'a T>>(&mut self, iter: I) -> Result<(), TryExtendIter<I>> where T: Copy + 'a {
		todo!()
	}

	/// Consumes the deque, returning an iterator over its contents.
	///
	/// # Errors
	///
	/// Returns an error if the deque holds a shared reference to its buffer.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque: ArrayDeque<i32, 3> = ArrayDeque::from([1, 2, 3]);
	/// let mut iter = deque.try_into_iter().unwrap();
	/// assert!(iter.eq([1, 2, 3]));
	/// ```
	pub fn try_into_iter(self) -> Result<IntoIter<T, N, A, ATOMIC>, Self> {
		todo!()
	}

	/// Converts the fixed-capacity deque into a variable-capacity deque of capacity `N`.
	///
	/// This may be done even when the deque is shared. This operation takes *O*(1) time, and does
	/// not allocate memory.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let array_deque: ArrayDeque<i32, 3> = ArrayDeque::from([1, 2, 3]);
	/// let mut deque = array_deque.into_deque();
	/// assert_eq!(deque.capacity(), 3);
	/// // The deque can now grow its capacity beyond the initial fixed capacity.
	/// assert_eq!(deque.try_push_back(4), Ok(()));
	/// ```
	#[cfg(feature = "deque")]
	pub fn into_deque(self) -> Deque<T, ATOMIC, A> {
		todo!()
	}
}

impl<T: Clone, const N: usize, A: Allocator, const ATOMIC: bool> ArrayDeque<T, N, ATOMIC, A> {
	/// Resizes the deque in-place to the specified length, cloning `value` into additional space as
	/// needed.
	///
	/// If `new_len` is greater than the current length, the deque is extended, filling the
	/// additional space with `value`. If `new_len` is less than the current length, the deque is
	/// truncated.
	///
	/// # Leaking
	///
	/// If the deque is truncated, the same leaking caveats as [`truncate`] apply.
	///
	/// [`truncate`]: Self::truncate#leaking
	///
	/// # Errors
	///
	/// Returns [`Shared`] if the deque is immutable because it holds a shared reference to its
	/// buffer. Returns [`FullCapacity`] if the new length would be larger than the fixed capacity
	/// of the deque. In this case, the deque is filled completely.
	/// 
	/// [`Shared`]: TryExtend::Shared
	/// [`FullCapacity`]: TryExtend::FullCapacity
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::TryExtend;
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque: ArrayDeque<i32, 8> = ArrayDeque::new();
	/// deque.try_extend([1, 2, 3]).unwrap();
	///
	/// assert_eq!(deque.try_resize(5, 0), Ok(()));
	/// assert_eq!(deque, [1, 2, 3, 0, 0]);
	/// assert_eq!(deque.try_resize(3, 0), Ok(()));
	/// assert_eq!(deque, [1, 2, 3]);
	/// assert_eq!(deque.try_resize(16, 0), Err(TryExtend::FullCapacity { remaining: 8 }));
	/// assert_eq!(deque, [1, 2, 3, 0, 0, 0, 0, 0]);
	/// ```
	pub fn try_resize(&mut self, new_len: usize, value: T) -> Result<(), TryExtend> {
		todo!()
	}

	/// Clones and appends all elements in a slice to the back of the deque.
	///
	/// # Errors
	///
	/// Returns [`FullCapacity`] if the deque is filled before the full slice could be appended. In
	/// this case, the deque is filled completely and the error contains the number of elements
	/// remaining. [`Shared`] is returned if the deque is immutable because it holds a shared
	/// reference to its buffer.
	/// 
	/// [`FullCapacity`]: TryExtend::FullCapacity
	/// [`Shared`]: TryExtend::Shared
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::TryExtend;
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque: ArrayDeque<i32, 4> = ArrayDeque::new();
	/// assert_eq!(deque.try_extend_from_slice(&[1, 2, 3]), Ok(()));
	/// assert_eq!(deque.try_extend_from_slice(&[4, 5, 6]), Err(TryExtend::FullCapacity { remaining: 2 }));
	/// assert_eq!(deque, [1, 2, 3, 4]);
	/// ```
	pub fn try_extend_from_slice(&mut self, other: &[T]) -> Result<(), TryExtend> {
		todo!()
	}
	/// Clones and appends elements from `range` to the back of the deque.
	///
	/// # Panics
	///
	/// Panics if the start of the range is greater than the end or if the end of the range is
	/// greater than the length of the deque.
	///
	/// # Errors
	///
	/// Returns [`FullCapacity`] if the deque is filled before the full range could be appended. In
	/// this case, the deque is filled completely and the error contains the number of elements
	/// remaining. [`Shared`] is returned if the deque is immutable because it holds a shared
	/// reference to its buffer.
	/// 
	/// [`FullCapacity`]: TryExtend::FullCapacity
	/// [`Shared`]: TryExtend::Shared
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::TryExtend;
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque: ArrayDeque<i32, 8> = ArrayDeque::new();
	/// deque.try_extend([1, 2, 3, 4]).unwrap();
	/// assert_eq!(deque.try_extend_from_within(1..3), Ok(()));
	/// assert_eq!(deque, [1, 2, 3, 4, 2, 3]);
	/// assert_eq!(deque.try_extend_from_within(0..3), Err(TryExtend::FullCapacity { remaining: 1 }));
	/// assert_eq!(deque, [1, 2, 3, 4, 2, 3, 1, 2]);
	/// ```
	pub fn try_extend_from_within<R: RangeBounds<usize>>(&mut self, range: R) -> Result<(), TryExtend> {
		todo!()
	}
}

// CoW operations
impl<T: Clone, const N: usize, A: Allocator + Clone, const ATOMIC: bool> ArrayDeque<T, N, ATOMIC, A> {
	/// Returns a pair of mutable slices over the contents of the deque.
	///
	/// If the deque is contiguous, all elements of the deque will be in the first slice and the
	/// second will be empty.
	///
	/// If the deque is shared, its contents are cloned. A fallible version is also provided:
	/// [`try_as_mut_slices`].
	///
	/// [`try_as_mut_slices`]: Self::try_as_mut_slices
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque = ArrayDeque::<_, 4>::new();
	/// _ = deque.push_back(0);
	/// _ = deque.push_back(1);
	///
	/// _ = deque.push_front(10);
	/// _ = deque.push_front(9);
	///
	/// deque.as_mut_slices().0[0] = 42;
	/// deque.as_mut_slices().1[0] = 24;
	///
	/// assert_eq!(deque.as_slices(), (&[42, 10][..], &[24, 1][..]));
	/// ```
	pub fn as_mut_slices(&mut self) -> (&mut [T], &mut [T]) {
		todo!()
	}

	/// Clones the deque contents out of a shared allocation, making the deque mutable. Returns an
	/// "always-mutable" view into the deque.
	///
	/// To return an error if the deque is shared, without allocating or cloning, use [`unique`]
	/// instead.
	///
	/// [`unique`]: Self::unique
	///
	/// # Panics
	///
	/// Panics if allocation fails, for example in an out-of-memory condition.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque: ArrayDeque<i32, 3> = ArrayDeque::from([1, 2, 3]);
	/// let clone = deque.clone();
	///
	/// let mut unique = deque.as_unique();
	/// unique.clear();
	/// unique.extend_from_slice(&[4, 5, 6]).unwrap();
	/// assert!(deque.is_unique());
	/// assert_eq!(deque, [4, 5, 6]);
	///
	/// // The first deque's contents have been cloned and are no longer shared
	/// // with the second.
	/// assert!(clone.is_unique());
	/// assert_ne!(deque, clone);
	/// ```
	pub fn as_unique(&mut self) -> Unique<T, N, A, ATOMIC> {
		todo!()
	}

	/// Clones the deque contents out of a shared allocation, making the deque mutable. Returns an
	/// "always-mutable" view into the deque.
	///
	/// # Errors
	///
	/// Returns an error if allocation fails, for example in an out-of-memory condition.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque: ArrayDeque<i32, 3> = ArrayDeque::from([1, 2, 3]);
	/// let clone = deque.clone();
	///
	/// let mut unique = deque.try_as_unique().expect("allocation failed");
	/// unique.clear();
	/// unique.extend_from_slice(&[4, 5, 6]).unwrap();
	/// assert!(deque.is_unique());
	/// assert_eq!(deque, [4, 5, 6]);
	///
	/// // The first deque's contents have been cloned and are no longer shared
	/// // with the second.
	/// assert!(clone.is_unique());
	/// assert_ne!(deque, clone);
	/// ```
	pub fn try_as_unique(&mut self) -> Result<Unique<T, N, A, ATOMIC>, AllocError> {
		todo!()
	}

	/// Gets a mutable reference to the element at `index`, where index `0` is the front of the
	/// queue.
	///
	/// If the index is in bounds and the deque is shared, its contents are cloned. A fallible
	/// version is also provided: [`try_get_mut`].
	///
	/// [`try_get_mut`]: Self::try_get_mut
	///
	/// # Panics
	///
	/// Panics if allocation fails, for example in an out-of-memory condition.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque = ArrayDeque::from([1, 2, 3]);
	///
	/// if let Some(v) = deque.get_mut(1) {
	///     *v = 4;
	/// }
	/// assert_eq!(deque, [1, 4, 3]);
	/// ```
	pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
		todo!()
	}
	/// Returns a mutable reference to the front element, or `None` if the deque is empty.
	///
	/// If the deque is shared and not empty, its contents are cloned. A fallible version is also
	/// provided: [`try_front_mut`].
	///
	/// [`try_front_mut`]: Self::try_front_mut
	///
	/// # Panics
	///
	/// Panics if allocation fails, for example in an out-of-memory condition.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque = ArrayDeque::from([1, 2, 3]);
	///
	/// if let Some(v) = deque.front_mut() {
	///     *v = 4;
	/// }
	/// assert_eq!(deque, [4, 2, 3]);
	/// ```
	pub fn front_mut(&mut self) -> Option<&mut T> {
		self.get_mut(0)
	}
	/// Returns a mutable reference to the back element, or `None` if the deque is empty.
	///
	/// If the deque is shared and not empty, its contents are cloned. A fallible version is also
	/// provided: [`try_back_mut`].
	///
	/// [`try_back_mut`]: Self::try_back_mut
	///
	/// # Panics
	///
	/// Panics if allocation fails, for example in an out-of-memory condition.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque = ArrayDeque::from([1, 2, 3]);
	///
	/// if let Some(v) = deque.back_mut() {
	///     *v = 4;
	/// }
	/// assert_eq!(deque, [1, 2, 4]);
	/// ```
	pub fn back_mut(&mut self) -> Option<&mut T> {
		todo!()
	}

	/// Returns an iterator returning mutable references to elements front-to-back.
	///
	/// If the deque is shared and not empty, its contents are cloned. A fallible version is also
	/// provided: [`try_iter_mut`].
	///
	/// [`try_iter_mut`]: Self::try_iter_mut
	///
	/// # Panics
	///
	/// Panics if allocation fails, for example in an out-of-memory condition.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque: ArrayDeque<i32, 3> = ArrayDeque::from([1, 2, 3]);
	///
	/// for v in deque.iter_mut() {
	///     *v *= 2;
	/// }
	///
	/// assert_eq!(deque, [2, 4, 6]);
	/// ```
	// Todo: lazily clone out of shared allocation only when Iterator::next is called?
	pub fn iter_mut(&mut self) -> IterMut<T> {
		todo!()
	}

	/// Returns an iterator returning mutable references to elements within a range.
	///
	/// If the range is not empty and the deque is shared, its contents are cloned. A fallible
	/// version is also provided: [`try_range_mut`].
	///
	/// [`try_range_mut`]: Self::try_range_mut
	///
	/// # Panics
	///
	/// Panics if:
	/// - allocation fails, for example in an out-of-memory condition
	/// - the starting point is greater than the end point or if the end point is greater than the
	///   length of the deque
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque = ArrayDeque::from([1, 2, 3]);
	/// for v in deque.range_mut(2..) {
	///     *v *= 2;
	/// }
	/// assert_eq!(deque, [1, 2, 6]);
	/// ```
	pub fn range_mut<R: RangeBounds<usize>>(&mut self, range: R) -> IterMut<T> {
		todo!()
	}

	/// Prepends an element to the deque, returning the element back if the deque is full.
	///
	/// If the deque is shared and has spare capacity, its contents are cloned. A fallible version
	/// is also provided: [`try_push_front`].
	///
	/// [`try_push_front`]: Self::try_push_front
	///
	/// # Errors
	///
	/// If the deque is full, `element` is returned and the deque is not modified.
	///
	/// # Panics
	///
	/// Panics if allocation fails, for example in an out-of-memory condition.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque = ArrayDeque::<_, 2>::new();
	/// assert_eq!(deque.push_front(1), Ok(()));
	/// assert_eq!(deque.push_front(2), Ok(()));
	/// assert_eq!(deque.push_front(3), Err(3));
	/// assert_eq!(deque, [2, 1]);
	/// ```
	pub fn push_front(&mut self, value: T) -> Result<(), T> {
		todo!()
	}
	/// Appends an element to the back of the deque.
	///
	/// If the deque is shared and has spare capacity, its contents are cloned. A fallible version
	/// is also provided: [`try_push_back`].
	///
	/// [`try_push_back`]: Self::try_push_back
	///
	/// # Errors
	///
	/// If the deque is full, `element` is returned and the deque is not modified.
	///
	/// # Panics
	///
	/// Panics if allocation fails, for example in an out-of-memory condition.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque = ArrayDeque::<_, 2>::new();
	/// assert_eq!(deque.push_back(1), Ok(()));
	/// assert_eq!(deque.push_back(2), Ok(()));
	/// assert_eq!(deque.push_back(3), Err(3));
	/// assert_eq!(deque, [1, 2]);
	/// ```
	pub fn push_back(&mut self, value: T) -> Result<(), T> {
		todo!()
	}

	/// Swaps elements at indices `i` and `j`, where index `0` is the front of the queue. Both may
	/// be equal.
	///
	/// If the indices are not equal and the deque is shared, its contents are cloned. A fallible
	/// version is also provided: [`try_swap`].
	///
	/// [`try_swap`]: Self::try_swap
	///
	/// # Panics
	///
	/// Panics if:
	/// - allocation fails, for example in an out-of-memory condition
	/// - either index is out of bounds.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut buf = ArrayDeque::from([1, 2, 3]);
	/// assert_eq!(buf, [1, 2, 3]);
	/// buf.swap(0, 2);
	/// assert_eq!(buf, [3, 2, 1]);
	/// ```
	pub fn swap(&mut self, i: usize, j: usize) {
		todo!()
	}

	/// Removes and returns the element at `index` from the deque, replacing it with the first
	/// element. Index `0` is at the front of the queue. This does not preserve ordering, but is
	/// *O*(1).
	///
	/// Returns `None` if `index` is out of bounds.
	///
	/// If the index is in bounds and the deque is shared, its contents may be cloned. A fallible
	/// version is also provided: [`try_swap_remove_front`].
	///
	/// [`try_swap_remove_front`]: Self::try_swap_remove_front
	///
	/// # Panics
	///
	/// Panics if allocation fails, for example in an out-of-memory condition.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque = ArrayDeque::from([1, 2, 3]);
	/// assert_eq!(deque.swap_remove_front(2), Some(3));
	/// assert_eq!(deque, [2, 1]);
	/// deque.clear();
	/// assert_eq!(deque.swap_remove_front(0), None);
	/// ```
	// Todo: when removing the front element (no swap), skip cloning the whole buffer as pop_front
	//  does. Avoid leaking non-trivial Drop types by cloning the whole buffer for these.
	pub fn swap_remove_front(&mut self, index: usize) -> Option<T> {
		todo!()
	}
	/// Removes and returns the element at `index` from the deque, replacing it with the last
	/// element. Index `0` is at the front of the queue. This does not preserve ordering, but is
	/// *O*(1).
	///
	/// Returns `None` if `index` is out of bounds.
	///
	/// If the index is in bounds and the deque is shared, its contents may be cloned. A fallible
	/// version is also provided: [`try_swap_remove_back`].
	///
	/// [`try_swap_remove_back`]: Self::try_swap_remove_back
	///
	/// # Panics
	///
	/// Panics if allocation fails, for example in an out-of-memory condition.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque = ArrayDeque::from([1, 2, 3]);
	/// assert_eq!(deque.swap_remove_back(0), Some(1));
	/// assert_eq!(deque, [3, 2]);
	/// deque.clear();
	/// assert_eq!(deque.swap_remove_back(0), None);
	/// ```
	// Todo: when removing the back element (no swap), skip cloning the whole buffer as pop_back
	//  does. Avoid leaking non-trivial Drop types by cloning the whole buffer for these.
	pub fn swap_remove_back(&mut self, index: usize) -> Option<T> {
		todo!()
	}

	/// Removes and returns the element `index` from the deque, shifting subsequent elements at
	/// whichever end is closer to the removal point. Index `0` is at the front of the queue.
	///
	/// Returns `None` if `index` is out of bounds.
	///
	/// If the index is in bounds and the deque is shared, its contents may be cloned. A fallible
	/// version is also provided: [`try_remove`].
	///
	/// [`try_remove`]: Self::try_remove
	///
	/// # Panics
	///
	/// Panics if allocation fails, for example in an out-of-memory condition.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque = ArrayDeque::from([1, 2, 3]);
	/// assert_eq!(deque.remove(1), Some(2));
	/// assert_eq!(deque, [1, 3]);
	/// ```
	// Todo: when removing the front or back element (no shift), skip cloning the whole buffer as
	//  pop_front and pop_back do. Avoid leaking non-trivial Drop types by cloning the whole buffer
	//  for these.
	pub fn remove(&mut self, index: usize) -> Option<T> {
		todo!()
	}

	/// Inserts an element at position `index` within the deque, shifting subsequent elements toward
	/// the back.
	///
	/// If the deque is shared, its contents will be cloned. A fallible version is also provided:
	/// [`try_insert`].
	///
	/// [`try_insert`]: Self::try_insert
	///
	/// # Errors
	///
	/// If the deque is full, `element` is returned and the deque is not modified.
	///
	/// # Panics
	///
	/// Panics if:
	/// - allocation fails, for example in an out-of-memory condition
	/// - `index` is greater than the deque length
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque: ArrayDeque<i32, 4> = ArrayDeque::new();
	/// assert_eq!(deque.push_back(1), Ok(()));
	/// assert_eq!(deque.push_back(3), Ok(()));
	/// assert_eq!(deque.push_back(4), Ok(()));
	/// assert_eq!(deque, [1, 3, 4]);
	///
	/// assert_eq!(deque.insert(1, 2), Ok(()));
	/// assert_eq!(deque.insert(2, 0), Err(0));
	/// assert_eq!(deque, [1, 2, 3, 4]);
	/// ```
	pub fn insert(&mut self, index: usize, element: T) -> Result<(), T> {
		todo!()
	}

	/// Retains the elements specified by `predicate`, dropping the rest.
	///
	/// Removes all elements `e` for which `predicate(&e)` returns `false`. This method operates
	/// in-place, visiting each element exactly once in the original order, and preserves the order
	/// of the retained elements.
	///
	/// If the deque is shared, its contents will be cloned. A fallible version is also provided:
	/// [`try_retain`].
	///
	/// [`try_retain`]: Self::try_retain
	///
	/// # Panics
	///
	/// Panics if allocation fails, for example in an out-of-memory condition.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque: ArrayDeque<i32, 4> = ArrayDeque::from([1, 2, 3, 4]);
	/// deque.retain(|&x| x % 2 == 0);
	/// assert_eq!(deque, [2, 4]);
	/// ```
	pub fn retain<F: FnMut(&T) -> bool>(&mut self, predicate: F) {
		todo!()
	}

	/// Retains the elements specified by `predicate`, dropping the rest.
	///
	/// Removes all elements `e` for which `predicate(&mut e)` returns `false`. This method operates
	/// in-place, visiting each element exactly once in the original order, and preserves the order
	/// of the retained elements.
	///
	/// If the deque is shared, its contents will be cloned. A fallible version is also provided:
	/// [`try_retain_mut`].
	///
	/// [`try_retain_mut`]: Self::try_retain_mut
	///
	/// # Panics
	///
	/// Panics if allocation fails, for example in an out-of-memory condition.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque: ArrayDeque<i32, 4> = ArrayDeque::from([1, 2, 3, 4]);
	/// deque.retain_mut(|x| if *x % 2 == 0 {
	///     *x += 1;
	///     true
	/// } else {
	///     false
	/// });
	/// assert_eq!(deque, [3, 5]);
	/// ```
	pub fn retain_mut<F: FnMut(&mut T) -> bool>(&mut self, predicate: F) {
		todo!()
	}

	/// Moves all elements from `other` into the deque, leaving `other` empty. Any atomic vector
	/// type from this crate may be appended, even array vectors/deques with a different fixed
	/// capacity.
	///
	/// If one vector/deque is shared, its elements are cloned into the unique one. If both are
	/// shared, their contents will be cloned into a unique allocation. A fallible version is also
	/// provided: [`try_append`].
	///
	/// [`try_append`]: Self::try_append
	///
	/// # Leaking
	///
	/// If one vector/deque is shared, it is effectively [`clear`]ed, causing all its elements to go
	/// out of scope without dropping. The elements' [`Drop`] implementation can only be safely called
	/// when both vectors/deques hold a unique reference.
	///
	/// Rust does not require [`Drop::drop`] to be called, but this may be undesirable behavior for
	/// types with a non-trivial `drop` implementation. For such types, use [`unique`]/[`as_unique`]
	/// to get a mutable view which is guaranteed to drop elements, or [`is_unique`] to check for a
	/// unique reference.
	///
	/// [`clear`]: Self::clear
	/// [`unique`]: Self::unique
	/// [`as_unique`]: Self::as_unique
	/// [`is_unique`]: Self::is_unique
	///
	/// # Errors
	///
	/// Returns an error if the deque would overflow its fixed capacity after appending `other`. In
	/// this case, neither vector/deque is modified.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::FullCapacity;
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque1: ArrayDeque<i32, 7> = ArrayDeque::new();
	/// deque1.extend([1, 2, 3]);
	/// let mut deque2 = ArrayDeque::from([4, 5, 6]);
	/// let mut deque3 = ArrayDeque::from([7, 8, 9]);
	/// assert_eq!(deque1.append(&mut deque2), Ok(()));
	/// assert_eq!(deque1, [1, 2, 3, 4, 5, 6]);
	/// assert_eq!(deque2, []);
	///
	/// assert_eq!(deque2.append(&mut deque3), Err(FullCapacity { remaining: 2 }));
	/// assert_eq!(deque1, [1, 2, 3, 4, 5, 6, 7]);
	/// assert_eq!(deque3, [8, 9]);
	/// ```
	pub fn append<V: RcVector<T, A, ATOMIC> + ?Sized>(&mut self, other: &mut V) -> Result<(), FullCapacity> {
		todo!()
	}

	/// Removes the specified range from the deque, returning all removed elements as an iterator.
	/// If the iterator is dropped before being fully consumed, the remaining removed elements are
	/// dropped.
	///
	/// If range is not empty and the deque is shared, the kept elements will be cloned into a
	/// unique allocation before draining, and returned elements will be cloned out of the shared
	/// deque. A fallible version is also provided: [`try_drain`].
	///
	/// [`try_drain`]: Self::try_drain
	///
	/// # Panics
	///
	/// Panics if allocation fails, for example in an out-of-memory condition.
	///
	/// # Leaking
	///
	/// If the returned iterator goes out of scope without being dropped (due to [`forget`], for
	/// example), the deque may have lost and leaked elements arbitrarily, including elements outside
	/// the range.
	///
	/// [`forget`]: core::mem::forget
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque: ArrayDeque<i32, 8> = ArrayDeque::from([1, 2, 3, 4, 5, 6, 7, 8]);
	/// let removed = deque.drain(2..6);
	/// assert!(removed.eq([3, 4, 5, 6]));
	/// assert_eq!(deque, [1, 2, 7, 8]);
	/// ```
	pub fn drain<R: RangeBounds<usize>>(&mut self, range: R) -> Drain<T, N, A, ATOMIC> {
		todo!()
	}

	/// Splits the deque into two at the given index.
	///
	/// Returns a new deque containing the elements starting from the given index. The original is
	/// left containing the elements up to `at` (exclusive).
	///
	/// - If you want to take ownership of the entire contents and capacity of the deque, use
	///   [`mem::take`] or [`mem::replace`].
	/// - If you don't need the returned deque at all, see [`truncate`].
	/// - If you want to take ownership of an arbitrary range, or you don't necessarily want to
	///   store the removed items, see [`drain`].
	///
	/// If the deque is shared, the elements after `at` are cloned into the returned deque. The
	/// remaining contents of the original deque may be cloned into a unique allocation. A fallible
	/// version is also provided: [`try_split_off`].
	///
	/// [`mem::take`]: core::mem::take
	/// [`mem::replace`]: core::mem::replace
	/// [`truncate`]: Self::truncate
	/// [`drain`]: Self::drain
	/// [`try_split_off`]: Self::try_split_off
	///
	/// # Panics
	///
	/// Panics if:
	/// - allocation fails, for example in an out-of-memory condition
	/// - `at` is greater than the deque length
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque = ArrayDeque::from([1, 2, 3, 4]);
	/// assert_eq!(deque.split_off(2), [3, 4]);
	/// assert_eq!(deque, [1, 2]);
	/// ```
	#[must_use = "use `.truncate()` if you don't need the other half"]
	pub fn split_off(&mut self, at: usize) -> Self {
		todo!()
	}

	/// Resizes the deque in-place to the specified length.
	///
	/// If `new_len` is greater than the current length, the deque is extended, filling the
	/// additional space with element returned from calling the closure `fill`. If `new_len` is less
	/// than the current length, the deque is truncated.
	///
	/// To fill the additional space by [`Clone`]ing a given value, use [`resize`]. To fill with
	/// default values, pass [`Default::default`] as the second argument.
	///
	/// If the deque is shared but must be extended, its contents are first cloned before new
	/// elements are added. A fallible version is also provided: [`try_resize_with`].
	///
	/// [`resize`]: Self::resize
	/// [`try_resize_with`]: Self::try_resize_with
	///
	/// # Panics
	///
	/// Panics if allocation fails, for example in an out-of-memory condition.
	///
	/// # Leaking
	///
	/// If the deque is truncated, the same leaking caveats as [`truncate`] apply.
	///
	/// [`truncate`]: Self::truncate#leaking
	///
	/// # Errors
	///
	/// Returns an error if the new length would be larger than the fixed capacity of the deque. In
	/// this case, the deque is filled completely.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::FullCapacity;
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque: ArrayDeque<i32, 8> = ArrayDeque::new();
	/// deque.extend([1, 2, 3]);
	/// let fill = Default::default;
	///
	/// assert_eq!(deque.resize_with(5, fill), Ok(()));
	/// assert_eq!(deque, [1, 2, 3, 0, 0]);
	/// assert_eq!(deque.resize_with(3, fill), Ok(()));
	/// assert_eq!(deque, [1, 2, 3]);
	/// assert_eq!(deque.resize_with(16, fill), Err(FullCapacity { remaining: 8 }));
	/// assert_eq!(deque, [1, 2, 3, 0, 0, 0, 0, 0]);
	/// ```
	pub fn resize_with<F: FnMut() -> T>(&mut self, new_len: usize, fill: F) -> Result<(), FullCapacity> {
		todo!()
	}

	/// Resizes the deque in-place to the specified length, cloning `value` into additional space
	/// as needed.
	///
	/// If `new_len` is greater than the current length, the deque is extended, filling the
	/// additional space with `value`. If `new_len` is less than the current length, the deque is
	/// truncated.
	///
	/// If the deque is shared but must be extended, its contents are first cloned before new
	/// elements are added. A fallible version is also provided: [`try_resize`].
	///
	/// [`try_resize`]: Self::try_resize
	///
	/// # Panics
	///
	/// Panics if allocation fails, for example in an out-of-memory condition.
	///
	/// # Leaking
	///
	/// If the deque is truncated, the same leaking caveats as [`truncate`] apply.
	///
	/// [`truncate`]: Self::truncate#leaking
	///
	/// # Errors
	///
	/// Returns an error if the new length would be larger than the fixed capacity of the deque. In
	/// this case, the deque is filled completely.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::FullCapacity;
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque: ArrayDeque<i32, 8> = ArrayDeque::new();
	/// deque.extend([1, 2, 3]);
	///
	/// assert_eq!(deque.resize(5, 0), Ok(()));
	/// assert_eq!(deque, [1, 2, 3, 0, 0]);
	/// assert_eq!(deque.resize(3, 0), Ok(()));
	/// assert_eq!(deque, [1, 2, 3]);
	/// assert_eq!(deque.resize(16, 0), Err(FullCapacity { remaining: 8 }));
	/// assert_eq!(deque, [1, 2, 3, 0, 0, 0, 0, 0]);
	/// ```
	pub fn resize(&mut self, new_len: usize, value: T) -> Result<(), FullCapacity> {
		todo!()
	}

	/// Rearranges the contents of the deque such that they are stored in a single contiguous slice,
	/// returning the slice. The order of the elements in the deque is preserved; only the internal
	/// storage is changed.
	///
	/// Once the internal storage is contiguous, the [as_slices] and [as_mut_slices] will return the
	/// entire contents of the deque in a single slice.
	///
	/// If the deque is shared but must be rearranged, its contents are cloned. A fallible version
	/// is also provided: [`try_make_contiguous`].
	///
	/// [as_slices]: Self::as_slices
	/// [as_mut_slices]: Self::as_mut_slices
	/// [try_make_contiguous]: Self::try_make_contiguous
	///
	/// # Panics
	///
	/// Panics if allocation fails, for example in an out-of-memory condition.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque: ArrayDeque<i32, 3> = ArrayDeque::new();
	///
	/// _ = deque.push_back(2);
	/// _ = deque.push_back(1);
	/// _ = deque.push_front(3);
	/// assert_eq!(deque.as_slices(), (&[2, 1][..], &[3][..]));
	///
	/// deque.make_contiguous();
	/// assert_eq!(deque.as_slices(), (&[3, 2, 1][..], &[][..]));
	/// ```
	pub fn make_contiguous(&mut self) -> &mut [T] {
		todo!()
	}

	/// Rotates the deque contents `n` places to the left, such that the element at index `n` is the
	/// first element. This is equivalent to rotating right by `len() - n`.
	///
	/// If the deque is shared, its contents are cloned. A fallible version is also provided:
	/// [`try_rotate_left`].
	///
	/// [`try_rotate_left`]: Self::try_rotate_left
	///
	/// # Panics
	///
	/// Panics if:
	/// - allocation fails, for example in an out-of-memory condition
	/// - `n` is greater than the length of the deque. When `n` is equal to the length, this
	///   operation simply does nothing *without* panicking
	///
	/// # Time complexity
	///
	/// Takes *O*(`min(n, len() - n)`) time.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::arc::ArrayDeque;
	///
	/// let mut deque: ArrayDeque<i32, 10> = (0..10).collect();
	///
	/// deque.rotate_left(3);
	/// assert_eq!(deque, [3, 4, 5, 6, 7, 8, 9, 0, 1, 2]);
	///
	/// for i in 1..10 {
	///     assert_eq!(i * 3 % 10, deque[0]);
	///     deque.rotate_left(3);
	/// }
	/// assert_eq!(deque, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]);
	/// ```
	pub fn rotate_left(&mut self, n: usize) {
		todo!()
	}
	/// Rotates the deque contents `n` places to the right, such that the first element is at index
	/// `n`. This is equivalent to rotating left by `len() - n`.
	///
	/// If the deque is shared, its contents are cloned. A fallible version is also provided:
	/// [`try_rotate_right`].
	///
	/// [`try_rotate_right`]: Self::try_rotate_right
	///
	/// # Panics
	///
	/// Panics if:
	/// - allocation fails, for example in an out-of-memory condition
	/// - `n` is greater than the length of the deque. When `n` is equal to the length, this
	///   operation simply does nothing *without* panicking.
	///
	/// # Time complexity
	///
	/// Takes *O*(`min(n, len() - n)`) time.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::arc::ArrayDeque;
	///
	/// let mut deque: ArrayDeque<i32, 10> = (0..10).collect();
	///
	/// deque.rotate_right(3);
	/// assert_eq!(deque, [7, 8, 9, 0, 1, 2, 3, 4, 5, 6]);
	///
	/// for i in 1..10 {
	///     assert_eq!(0, deque[i * 3 % 10]);
	///     deque.rotate_right(3);
	/// }
	/// assert_eq!(deque, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]);
	/// ```
	pub fn rotate_right(&mut self, n: usize) {
		todo!()
	}

	/// Clones and appends all elements in a slice to the back of the deque.
	///
	/// If the deque is shared, its contents are cloned. A fallible version is also provided:
	/// [`try_extend_from_slice`].
	///
	/// [`try_extend_from_slice`]: Self::try_extend_from_slice
	///
	/// # Panics
	///
	/// Panics if allocation fails, for example in an out-of-memory condition.
	///
	/// # Errors
	///
	/// Returns an error if the deque is filled before the full slice could be appended. In this
	/// case, the deque is filled completely and the error contains the number of elements remaining.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::FullCapacity;
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque: ArrayDeque<i32, 4> = ArrayDeque::new();
	/// assert_eq!(deque.extend_from_slice(&[1, 2, 3]), Ok(()));
	/// assert_eq!(deque.extend_from_slice(&[4, 5, 6]), Err(FullCapacity { remaining: 2 }));
	/// assert_eq!(deque, [1, 2, 3, 4]);
	/// ```
	pub fn extend_from_slice(&mut self, other: &[T]) -> Result<(), FullCapacity> {
		todo!()
	}
	/// Clones and appends elements from `range` to the end of the back of the deque.
	///
	/// If the deque is shared, its contents are cloned. A fallible version is also provided:
	/// [`try_extend_from_within`].
	///
	/// [`try_extend_from_within`]: Self::try_extend_from_within
	///
	/// # Panics
	///
	/// Panics if:
	/// - allocation fails, for example in an out-of-memory condition
	/// - the start of the range is greater than the end or if the end of the range is greater than
	///   the length of the deque
	///
	/// # Errors
	///
	/// Returns an error if the deque is filled before the full slice could be appended. In this
	/// case, the deque is filled completely and the error contains the number of elements remaining.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::FullCapacity;
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque: ArrayDeque<i32, 8> = ArrayDeque::new();
	/// deque.extend([1, 2, 3, 4]);
	/// assert_eq!(deque.extend_from_within(1..3), Ok(()));
	/// assert_eq!(deque, [1, 2, 3, 4, 2, 3]);
	/// assert_eq!(deque.extend_from_within(0..3), Err(FullCapacity { remaining: 1 }));
	/// assert_eq!(deque, [1, 2, 3, 4, 2, 3, 1, 2]);
	/// ```
	pub fn extend_from_within<R: RangeBounds<usize>>(&mut self, range: R) -> Result<(), FullCapacity> {
		todo!()
	}
}

impl<T: Clone, const N: usize, A: Allocator, const ATOMIC: bool> ArrayDeque<T, N, ATOMIC, A> {
	/// Removes the first element and returns it, or `None` if the deque is empty.
	///
	/// If the deque is shared, the element is cloned and returned. A fallible version is also
	/// provided: [`try_pop_front`].
	///
	/// [`try_pop_front`]: Self::try_pop_front
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque = ArrayDeque::from([1, 2]);
	/// assert_eq!(deque.pop_front(), Some(1));
	/// assert_eq!(deque.pop_front(), Some(2));
	/// assert_eq!(deque.pop_front(), None);
	/// ```
	// Todo: avoid leaking non-trivial Drop types by cloning the whole buffer. Otherwise, just clone
	//  the removed element out.
	pub fn pop_front(&mut self) -> Option<T> {
		todo!()
	}
	/// Removes the last element and returns it, or `None` if the deque is empty.
	///
	/// If the deque is shared, the element is cloned and returned. A fallible version is also
	/// provided: [`try_pop_back`].
	///
	/// [`try_pop_back`]: Self::try_pop_back
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut deque = ArrayDeque::from([1, 2]);
	/// assert_eq!(deque.pop_back(), Some(2));
	/// assert_eq!(deque.pop_back(), Some(1));
	/// assert_eq!(deque.pop_back(), None);
	/// ```
	// Todo: avoid leaking non-trivial Drop types by cloning the whole buffer. Otherwise, just clone
	//  the removed element out.
	pub fn pop_back(&mut self) -> Option<T> {
		todo!()
	}
}

impl<T, const N: usize, A: Allocator + Clone, const ATOMIC: bool> Clone for ArrayDeque<T, N, ATOMIC, A> {
	/// Creates a new deque sharing its contents with this deque.
	///
	/// If the fixed capacity is `0`, both deques remain unique.
	fn clone(&self) -> Self {
		todo!()
	}
}

impl<T: Hash, const N: usize, A: Allocator, const ATOMIC: bool> Hash for ArrayDeque<T, N, ATOMIC, A> {
	fn hash<H: Hasher>(&self, state: &mut H) {
		// Todo: use write_length_prefix when stable
		state.write_usize(self.len());
		for v in self.iter() {
			Hash::hash(v, state);
		}
	}
}

impl<T, const N: usize, A: Allocator, const ATOMIC: bool> Index<usize> for ArrayDeque<T, N, ATOMIC, A> {
	type Output = T;

	fn index(&self, index: usize) -> &Self::Output {
		self.get(index).expect("Out of bounds access")
	}
}

impl<T, const N: usize, const ATOMIC: bool> FromIterator<T> for ArrayDeque<T, N, ATOMIC> {
	fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
		todo!()
	}
}

impl<T: Clone, const N: usize, A: Allocator, const ATOMIC: bool> IntoIterator for ArrayDeque<T, N, ATOMIC, A> {
	type Item = T;
	type IntoIter = IntoIter<T, N, A, ATOMIC>;

	/// Consumes the deque into a front-to-back iterator yielding elements by value. If the deque is
	/// shared, the elements are cloned out of the deque.
	fn into_iter(self) -> Self::IntoIter {
		todo!()
	}
}

impl<'a, T, const N: usize, A: Allocator, const ATOMIC: bool> IntoIterator for &'a ArrayDeque<T, N, ATOMIC, A> {
	type Item = &'a T;
	type IntoIter = Iter<'a, T>;

	fn into_iter(self) -> Self::IntoIter {
		self.iter()
	}
}

impl<T: Clone, const N: usize, A: Allocator + Clone, const ATOMIC: bool> Extend<T> for ArrayDeque<T, N, ATOMIC, A> {
	fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
		todo!()
	}

	#[cfg(feature = "unstable-traits")]
	fn extend_reserve(&mut self, additional: usize) {
		todo!()
	}

	#[cfg(feature = "unstable-traits")]
	fn extend_one(&mut self, item: T) {
		todo!()
	}
}

impl<'a, T: Copy + 'a, const N: usize, A: Allocator + Clone, const ATOMIC: bool> Extend<&'a T> for ArrayDeque<T, N, ATOMIC, A> {
	fn extend<I: IntoIterator<Item = &'a T>>(&mut self, iter: I) {
		todo!()
	}

	#[cfg(feature = "unstable-traits")]
	fn extend_reserve(&mut self, additional: usize) {
		todo!()
	}

	#[cfg(feature = "unstable-traits")]
	fn extend_one(&mut self, item: &'a T) {
		todo!()
	}
}

impl<T: Eq, const N: usize, A: Allocator, const ATOMIC: bool> Eq for ArrayDeque<T, N, ATOMIC, A> { }

impl<T, const N1: usize, const N2: usize, A1, A2, const ATOMIC1: bool, const ATOMIC2: bool> PartialOrd<ArrayDeque<T, N2, ATOMIC2, A2>> for ArrayDeque<T, N1, ATOMIC1, A1>
where
	T: PartialOrd,
	A1: Allocator,
	A2: Allocator
{
	fn partial_cmp(&self, other: &ArrayDeque<T, N2, ATOMIC2, A2>) -> Option<Ordering> {
		todo!()
	}
}

impl<T: Ord, const N: usize, A: Allocator, const ATOMIC: bool> Ord for ArrayDeque<T, N, ATOMIC, A> {
	fn cmp(&self, other: &Self) -> Ordering {
		todo!()
	}
}

impl<T, const N: usize, A: Allocator, const ATOMIC: bool> Drop for ArrayDeque<T, N, ATOMIC, A> {
	fn drop(&mut self) {
		todo!()
	}
}

impl<T, const N: usize, const ATOMIC: bool> Default for ArrayDeque<T, N, ATOMIC> {
	fn default() -> Self {
		Self::new()
	}
}

impl<T: fmt::Debug, const N: usize, A: Allocator, const ATOMIC: bool> fmt::Debug for ArrayDeque<T, N, ATOMIC, A> {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		todo!()
	}
}

// Contiguous collection conversions

impl<T, const N: usize, A: Allocator, const ATOMIC: bool> From<ArrayVec<T, N, ATOMIC, A>> for ArrayDeque<T, N, ATOMIC, A> {
	fn from(value: ArrayVec<T, N, ATOMIC, A>) -> Self {
		todo!()
	}
}

impl<T, const N: usize, A: Allocator, const ATOMIC: bool> TryFrom<ArrayDeque<T, N, ATOMIC, A>> for ArrayVec<T, N, ATOMIC, A> {
	type Error = Shared<ArrayDeque<T, N, ATOMIC, A>>;

	/// Converts an [`ArrayDeque`] into an [`ArrayVec`].
	///
	/// # Errors
	///
	/// Returns an error containing the deque if it is not contiguous and holds a shared reference.
	fn try_from(mut value: ArrayDeque<T, N, ATOMIC, A>) -> Result<Self, Self::Error> {
		let Ok(_) = value.try_make_contiguous() else { return Err(Shared(value)) };
		todo!()
	}
}

impl<T, const N: usize, A: Allocator, const ATOMIC: bool> TryFrom<Vec<T, ATOMIC, A>> for ArrayDeque<T, N, ATOMIC, A> {
	type Error = Vec<T, ATOMIC, A>;

	/// Converts a variable-capacity vector into a fixed-capacity deque of capacity `N`.
	///
	/// # Errors
	///
	/// Returns the vector back if it is too large to fit in the fixed capacity `N`.
	fn try_from(value: Vec<T, ATOMIC, A>) -> Result<Self, Vec<T, ATOMIC, A>> {
		todo!()
	}
}

impl<T, const N: usize, A: Allocator, const ATOMIC: bool> TryFrom<ArrayDeque<T, N, ATOMIC, A>> for Vec<T, ATOMIC, A> {
	type Error = Shared<ArrayDeque<T, N, ATOMIC, A>>;

	/// Converts a fixed-capacity deque of capacity `N` into a variable-capacity vector.
	///
	/// # Errors
	///
	/// Returns an error containing the deque if it is not contiguous and holds a shared reference.
	fn try_from(mut value: ArrayDeque<T, N, ATOMIC, A>) -> Result<Self, Self::Error> {
		let Ok(_) = value.try_make_contiguous() else { return Err(Shared(value)) };
		todo!()
	}
}

// Var deque conversions

impl<T, const N: usize, A: Allocator, const ATOMIC: bool> TryFrom<Deque<T, ATOMIC, A>> for ArrayDeque<T, N, ATOMIC, A> {
	type Error = Deque<T, ATOMIC, A>;

	/// Converts a variable-capacity deque into a fixed-capacity deque of capacity `N`.
	///
	/// This may be done even when the deque is shared. This operation takes *O*(1) time, and does
	/// not allocate memory.
	///
	/// # Errors
	///
	/// Returns the deque back if its capacity is not equal to `N`.
	fn try_from(value: Deque<T, ATOMIC, A>) -> Result<Self, Deque<T, ATOMIC, A>> {
		todo!()
	}
}

impl<T, const N: usize, A: Allocator, const ATOMIC: bool> From<ArrayDeque<T, N, ATOMIC, A>> for Deque<T, ATOMIC, A> {
	/// Converts a fixed-capacity deque into a variable-capacity deque of capacity `N`.
	///
	/// This may be done even when the deque is shared. This operation takes *O*(1) time, and does
	/// not allocate memory.
	fn from(value: ArrayDeque<T, N, ATOMIC, A>) -> Self {
		todo!()
	}
}

// Array and slice conversions

impl<T: Clone, const N: usize, const ATOMIC: bool> From<&[T; N]> for ArrayDeque<T, N, ATOMIC> {
	fn from(value: &[T; N]) -> Self {
		todo!()
	}
}

impl<T: Clone, const N: usize, const ATOMIC: bool> From<&mut [T; N]> for ArrayDeque<T, N, ATOMIC> {
	fn from(value: &mut [T; N]) -> Self {
		todo!()
	}
}

impl<T, const N: usize, const ATOMIC: bool> From<[T; N]> for ArrayDeque<T, N, ATOMIC> {
	fn from(value: [T; N]) -> Self {
		todo!()
	}
}

impl<T: Clone, const N1: usize, const N2: usize, A: Allocator, const ATOMIC: bool> TryFrom<ArrayDeque<T, N1, ATOMIC, A>> for [T; N2] {
	type Error = ArrayDeque<T, N1, ATOMIC, A>;

	/// Converts an [`ArrayDeque`] into an array, cloning out of a shared allocation.
	///
	/// # Errors
	///
	/// Returns the deque back if its length is too large or small to fit in the array size.
	fn try_from(value: ArrayDeque<T, N1, ATOMIC, A>) -> Result<Self, Self::Error> {
		todo!()
	}
}

impl<T: Clone, const N: usize, const ATOMIC: bool> TryFrom<&[T]> for ArrayDeque<T, N, ATOMIC> {
	type Error = TryFromSlice<N>;

	fn try_from(value: &[T]) -> Result<Self, TryFromSlice<N>> {
		todo!()
	}
}

impl<T: Clone, const N: usize, const ATOMIC: bool> TryFrom<&mut [T]> for ArrayDeque<T, N, ATOMIC> {
	type Error = TryFromSlice<N>;

	fn try_from(value: &mut [T]) -> Result<Self, TryFromSlice<N>> {
		todo!()
	}
}

impl<const N: usize, const ATOMIC: bool> TryFrom<&str> for ArrayDeque<u8, N, ATOMIC> {
	type Error = TryFromSlice<N>;

	fn try_from(value: &str) -> Result<Self, Self::Error> {
		value.as_bytes().try_into()
	}
}

// Fallible Box/Vec conversions

impl<T, const N: usize, A: Allocator, const ATOMIC: bool> TryFrom<StdVec<T, A>> for ArrayDeque<T, N, ATOMIC, A> {
	type Error = StdVec<T, A>;

	/// Converts a [`Vec`] into a reference-counted, fixed-capacity deque.
	///
	/// # Errors
	///
	/// Returns the vector back if it is too large to fit in the fixed capacity `N`.
	///
	/// # Panics
	///
	/// Panics if allocation fails, for example in an out-of-memory condition.
	fn try_from(value: StdVec<T, A>) -> Result<Self, StdVec<T, A>> {
		todo!()
	}
}

impl<T, const N: usize, A: Allocator, const ATOMIC: bool> TryFrom<ArrayDeque<T, N, ATOMIC, A>> for StdVec<T, A> {
	type Error = Shared<ArrayDeque<T, N, ATOMIC, A>>;

	/// Converts a reference-counted, fixed-capacity deque of capacity `N` into a [`Vec`].
	///
	/// # Errors
	///
	/// Returns an error containing the deque if it holds a shared reference.
	///
	/// # Panics
	///
	/// Panics if allocation fails, for example in an out-of-memory condition.
	fn try_from(value: ArrayDeque<T, N, ATOMIC, A>) -> Result<Self, Self::Error> {
		todo!()
	}
}

impl<T, const N: usize, A: Allocator, const ATOMIC: bool> TryFrom<VecDeque<T, A>> for ArrayDeque<T, N, ATOMIC, A> {
	type Error = VecDeque<T, A>;

	/// Converts a [`VecDeque`] into a reference-counted, fixed-capacity deque.
	///
	/// # Errors
	///
	/// Returns the deque back if it is too large to fit in the fixed capacity `N`.
	fn try_from(value: VecDeque<T, A>) -> Result<Self, VecDeque<T, A>> {
		todo!()
	}
}

impl<T, const N: usize, A: Allocator, const ATOMIC: bool> TryFrom<ArrayDeque<T, N, ATOMIC, A>> for VecDeque<T, A> {
	type Error = Shared<ArrayDeque<T, N, ATOMIC, A>>;

	/// Converts a reference-counted, fixed-capacity deque of capacity `N` into a [`VecDeque`].
	///
	/// # Errors
	///
	/// Returns an error containing the deque if it holds a shared reference.
	///
	/// # Panics
	///
	/// Panics if allocation fails, for example in an out-of-memory condition.
	fn try_from(value: ArrayDeque<T, N, ATOMIC, A>) -> Result<Self, Self::Error> {
		todo!()
	}
}

impl<const N: usize, const ATOMIC: bool> TryFrom<String> for ArrayDeque<u8, N, ATOMIC> {
	type Error = String;

	fn try_from(value: String) -> Result<Self, String> {
		value.into_bytes()
			 .try_into()
			 .map_err(|v|
				 // Safety: the string was just converted into bytes and returned
				 // back as an error unmodified.
				 unsafe {
					 String::from_utf8_unchecked(v)
				 }
			 )
	}
}

// Not sure why Box gives a "conflicting implementation" error when it's generic over Allocator,
// so we'll leave these with the global allocator for now.

impl<T, const N: usize, const ATOMIC: bool> TryFrom<Box<[T]>> for ArrayDeque<T, N, ATOMIC> {
	type Error = Box<[T]>;

	fn try_from(value: Box<[T]>) -> Result<Self, Box<[T]>> {
		todo!()
	}
}

impl<T, const N: usize, const ATOMIC: bool> TryFrom<Box<[T; N]>> for ArrayDeque<T, N, ATOMIC> {
	type Error = Box<[T; N]>;

	fn try_from(value: Box<[T; N]>) -> Result<Self, Box<[T; N]>> {
		todo!()
	}
}

impl<const N: usize, const ATOMIC: bool> TryFrom<Box<str>> for ArrayDeque<u8, N, ATOMIC> {
	type Error = Box<str>;

	fn try_from(value: Box<str>) -> Result<Self, Box<str>> {
		Box::<[u8]>::from(value)
			.try_into()
			.map_err(|v|
				// Safety: the string was just converted into bytes and returned
				// back as an error unmodified.
				unsafe {
					core::mem::transmute(v)
				}
			)
	}
}
