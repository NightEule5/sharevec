// Copyright 2024 - Strixpyrr
// SPDX-License-Identifier: Apache-2.0

//! # Internal Layout
//!
//! The layout of the inner allocation is exactly equivalent to `Rc<(usize, usize, [T])>`, four
//! `usize` words plus the slice:
//!
//! ```text
//!  0        8       16       24       32..
//! |--------|--------|--------|--------|-------~
//! | strong |  weak  |  head  | length | slice..
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
use crate::array::deque::ArrayDeque;
use crate::array::vec::ArrayVec;
use crate::error::{Result, Shared};
use crate::marker::RcVector;
use crate::vec::Vec;
pub(crate) use __private::Deque;
use drain::Drain;
use into_iter::IntoIter;
pub use iter::{Iter, IterMut};
use unique::Unique;
use weak::Weak;

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

	pub struct Deque<T, const ATOMIC: bool, A: Allocator = Global> {
		pub(crate) inner: RawDeque<[T], A>,
		pub(crate) head: usize,
		pub(crate) len: usize,
	}
}

impl<T, const ATOMIC: bool> Deque<T, ATOMIC> {
	/// Creates a new, empty deque.
	///
	/// No memory is allocated until elements are pushed to the deque. Until memory is allocated,
	/// the deque and any of its clones act as if they hold a [unique](Self::is_unique) reference,
	/// despite lacking an allocation to reference. Thus, they are all mutable.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque: Deque<i32> = Deque::new();
	/// ```
	#[must_use]
	pub fn new() -> Self {
		todo!()
	}

	/// Constructs a new, empty deque with at least the specified capacity.
	///
	/// The deque will be able to hold at least `capacity` elements without reallocating. This
	/// method is allowed to allocate for more elements than the specified capacity. If the capacity
	/// is zero, the deque will not allocate. The same uniqueness rules as with [`new`] apply in this
	/// case.
	///
	/// If the vector element type is zero-sized, this will not allocate memory for any elements,
	/// and the capacity will always be [`usize::MAX`]. Memory will only be allocated for the
	/// reference counts.
	///
	/// [`new`]: Self::new
	///
	/// # Panics
	///
	/// Panics if the capacity is greater than [`isize::MAX`] *bytes* minus four [`usize`] words.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::with_capacity(10);
	///
	/// // The vector contains no items, but has space for at least 10
	/// assert_eq!(vec.len(), 0);
	/// assert!(vec.capacity() >= 10);
	///
	/// // These can be pushed without reallocating
	/// for i in 0..10 {
	///     vec.push(i);
	/// }
	/// assert_eq!(vec.len(), 10);
	/// assert!(vec.capacity() >= 10);
	///
	/// // Pushing one more element may cause the vector to reallocate
	/// vec.push(11);
	/// assert_eq!(vec.len(), 11);
	/// assert!(vec.capacity() >= 11);
	///
	/// // A vector of zero-sized elements will always over-allocate, as no
	/// // allocation is necessary
	/// let units: Vec<()> = Vec::with_capacity(10);
	/// assert_eq!(units.capacity(), usize::MAX);
	/// ```
	#[must_use]
	pub fn with_capacity(capacity: usize) -> Self {
		Self::with_capacity_in(capacity, Global)
	}
}

impl<T, A: Allocator, const ATOMIC: bool> Deque<T, ATOMIC, A> {
	/// Creates a new, empty deque with a fixed capacity in the given allocator.
	///
	/// No memory is allocated until elements are pushed to the deque. Until memory is allocated,
	/// the deque and any of its clones act as if they hold a [unique](Self::is_unique) reference,
	/// despite lacking an allocation to reference. Thus, they are all mutable.
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
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque: Deque<i32, _> = Deque::new_in(System);
	/// # }
	/// ```
	#[must_use]
	pub fn new_in(alloc: A) -> Self {
		todo!()
	}

	/// Constructs a new, empty vector with at least the specified capacity with the provided
	/// allocator.
	///
	/// The vector will be able to hold at least `capacity` elements without reallocating. This
	/// method is allowed to allocate for more elements than the specified capacity. If the capacity
	/// is zero, the vector will not allocate. The same uniqueness rules as with [`new`] apply in this
	/// case.
	///
	/// If the vector element type is zero-sized, this will not allocate memory for any elements,
	/// and the capacity will always be [`usize::MAX`]. Memory will only be allocated for the
	/// reference counts.
	///
	/// # Panics
	///
	/// Panics if the capacity is greater than [`isize::MAX`] *bytes* minus four [`usize`] words.
	///
	/// # Examples
	///
	/// ```
	/// #![feature(allocator_api)]
	///
	/// # #[cfg(feature = "std")]
	/// # {
	/// use std::alloc::System;
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32, _> = Vec::with_capacity_in(10, System);
	///
	/// // The vector contains no items, but has space for at least 10
	/// assert_eq!(vec.len(), 0);
	/// assert!(vec.capacity() >= 10);
	///
	/// // These can be pushed without reallocating
	/// for i in 0..10 {
	///     vec.push(i);
	/// }
	/// assert_eq!(vec.len(), 10);
	/// assert!(vec.capacity() >= 10);
	///
	/// // Pushing one more element may cause the vector to reallocate
	/// vec.push(11);
	/// assert_eq!(vec.len(), 11);
	/// assert!(vec.capacity() >= 11);
	///
	/// // A vector of zero-sized elements will always over-allocate, as no
	/// // allocation is necessary
	/// let units: Vec<(), _> = Vec::with_capacity_in(10, System);
	/// assert_eq!(units.capacity(), usize::MAX);
	/// # }
	/// ```
	pub fn with_capacity_in(capacity: usize, alloc: A) -> Self {
		todo!()
	}

	/// Returns the total number of elements the deque can hold.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque: Deque<i32> = Deque::with_capacity(8);
	/// assert!(deque.capacity() >= 8);
	/// ```
	pub const fn capacity(&self) -> usize {
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
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque: Deque<i32> = Deque::with_capacity(5);
	/// deque.push_back(0);
	/// deque.push_back(1);
	/// deque.push_back(2);
	///
	/// assert_eq!(deque.as_slices(), (&[0, 1, 2][..], &[][..]));
	///
	/// deque.push_front(10);
	/// deque.push_front(9);
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
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque: Deque<i32> = Deque::with_capacity(4);
	/// deque.push_back(0);
	/// deque.push_back(1);
	///
	/// deque.push_front(10);
	/// deque.push_front(9);
	///
	/// deque.try_as_mut_slices().unwrap().0[0] = 42;
	/// deque.try_as_mut_slices().unwrap().1[0] = 24;
	///
	/// assert_eq!(deque.as_slices(), (&[42, 10][..], &[24, 1][..]));
	/// ```
	pub fn try_as_mut_slices(&mut self) -> Result<(&mut [T], &mut [T])> {
		todo!()
	}

	/// Returns a raw pointer to the deque's buffer, or a dangling raw pointer valid for zero-sized
	/// reads if the deque didn't allocate.
	///
	/// The caller must ensure that the deque outlives the pointer this function returns, or else
	/// it will end up dangling. Modifying the deque may cause its buffer to be reallocated, which
	/// would also make any pointers to it invalid.
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
	/// use sharevec::deque::rc::Deque;
	///
	/// let deque: Deque<i32> = Deque::from([1, 2, 4]);
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
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque: Deque<i32> = Deque::from([1, 2, 3]);
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
	/// Returns a raw pointer to the deque's buffer, or a dangling raw pointer valid for zero-sized
	/// reads if the deque didn't allocate.
	///
	/// The caller must ensure that the deque outlives the pointer this function returns, or else
	/// it will end up dangling. Modifying the deque may cause its buffer to be reallocated, which
	/// would also make any pointers to it invalid.
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
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque: Deque<i32> = Deque::from([0; 8]);
	/// let ptr = deque.as_mut_ptr();
	///
	/// // Initialize elements via raw pointer writes.
	/// // This is safe because no other strong reference points to the vector contents.
	/// unsafe {
	///     for i in 0..deque.len() {
	///         ptr.add(i).write(i as i32);
	///     }
	/// }
	/// assert_eq!(deque, [1, 2, 3, 4, 5, 6, 7, 8]);
	/// ```
	///
	/// Due to the aliasing guarantee, this code is valid:
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque: Deque<i32> = Deque::from([0]);
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
	/// Returns a `NonNull` pointer to the deque's buffer, or a dangling [`NonNull`] pointer valid
	/// for zero-sized reads if the deque didn't allocate.
	///
	/// The caller must ensure that the deque outlives the pointer this function returns, or else
	/// will end up dangling. Modifying the deque may cause its buffer to be reallocated, which
	/// would also make any pointers to it invalid.
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
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque: Deque<i32> = Deque::from([0; 8]);
	/// let ptr = deque.as_non_null();
	///
	/// // Initialize elements via raw pointer writes.
	/// // This is safe because no other strong reference points to the vector contents.
	/// unsafe {
	///     for i in 0..deque.len() {
	///         ptr.add(i).write(i as i32);
	///     }
	/// }
	/// assert_eq!(deque, [1, 2, 3, 4, 5, 6, 7, 8]);
	/// ```
	///
	/// Due to the aliasing guarantee, this code is valid:
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque: Deque<i32> = Deque::from([0]);
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
	/// For empty deques created with [`new`]/[`new_in`] which have not been modified, this returns
	/// `true`.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let deque: Deque<i32> = Deque::with_capacity(10);
	/// let weak = deque.demote();
	/// assert!(deque.is_unique());
	/// ```
	///
	/// Non-allocated deques are always unique, even when cloned:
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let deque: Deque<i32> = Deque::new();
	/// let deque2 = deque.clone();
	/// assert!(deque.is_unique());
	/// assert!(deque2.is_unique());
	/// ```
	pub fn is_unique(&self) -> bool {
		self.strong_count() <= 1
	}
	/// Returns `true` if this deque does not hold the only reference to its allocated capacity,
	/// making it read-only. Only strong references count toward sharing.
	///
	/// For empty deques created with [`new`]/[`new_in`] which have not been modified, this returns
	/// `false`.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let deque: Deque<i32> = Deque::with_capacity(10);
	/// let clone = deque.clone();
	/// assert!(deque.is_shared());
	/// ```
	///
	/// Non-allocated deques are never shared, even when cloned:
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let deque: Deque<i32> = Deque::new();
	/// let deque2 = deque.clone();
	/// assert!(!deque.is_shared());
	/// assert!(!deque2.is_shared());
	/// ```
	pub fn is_shared(&self) -> bool {
		!self.is_unique()
	}
	/// Returns `true` if this deque's allocated capacity is *not* weakly referenced.
	///
	/// For empty deques created with [`new`]/[`new_in`] which have not been modified, this returns
	/// `true`.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let deque: Deque<i32> = Deque::with_capacity(10);
	/// assert!(deque.is_weakly_unique());
	/// ```
	///
	/// Non-allocated deques are never weakly referenced:
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let deque: Deque<i32> = Deque::new();
	/// let weak = deque.demote(); // Dangling
	/// assert!(deque.is_weakly_unique());
	/// ```
	pub fn is_weakly_unique(&self) -> bool {
		self.weak_count() == 0
	}
	/// Returns `true` if this deque's allocated capacity is weakly referenced.
	///
	/// For empty deques created with [`new`]/[`new_in`] which have not been modified, this returns
	/// `false`.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let deque: Deque<i32> = Deque::with_capacity(10);
	/// let weak = deque.demote();
	/// assert!(deque.is_weakly_shared());
	/// ```
	///
	/// Non-allocated deques are never weakly referenced:
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let deque: Deque<i32> = Deque::new();
	/// let weak = deque.demote(); // Dangling
	/// assert!(!deque.is_weakly_shared());
	/// ```
	pub fn is_weakly_shared(&self) -> bool {
		!self.is_weakly_unique()
	}

	/// Returns the number of strong references to the deque's allocated capacity.
	///
	/// For empty deques created with [`new`]/[`new_in`] which have not been modified, this returns
	/// `0`.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let deque: Deque<i32> = Deque::with_capacity(10);
	/// let clone = deque.clone();
	/// assert_eq!(deque.strong_count(), 2);
	/// ```
	///
	/// Non-allocated deques hold no strong references:
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let deque: Deque<i32> = Deque::new();
	/// assert_eq!(deque.strong_count(), 0);
	/// let deque2 = deque.clone();
	/// assert_eq!(deque.strong_count(), 0);
	/// assert_eq!(deque2.strong_count(), 0);
	/// ```
	pub fn strong_count(&self) -> usize {
		todo!()
	}
	/// Returns the number of weak references to the deque's allocated capacity.
	///
	/// For empty deques created with [`new`]/[`new_in`] which have not been modified, this returns
	/// `0`.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let deque: Deque<i32> = Deque::with_capacity(10);
	/// let weak = deque.demote();
	/// assert_eq!(deque.weak_count(), 1);
	/// ```
	///
	/// Non-allocated deques are never weakly referenced:
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let deque: Deque<i32> = Deque::new();
	/// let weak = deque.demote(); // Dangling
	/// assert_eq!(deque.weak_count(), 0);
	/// ```
	pub fn weak_count(&self) -> usize {
		todo!()
	}

	/// If the deque is unique, returns a mutable view of the unique allocation.
	///
	/// Any weak references are disassociated from the contents without cloning. See the note on
	/// [`Unique`] for details.
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
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque: Deque<i32> = Deque::new();
	///
	/// let mut unique = deque.unique().unwrap();
	/// unique.push_front(1);
	/// unique.push_front(2);
	/// drop(unique);
	///
	/// let clone = deque.clone();
	/// assert!(deque.unique().is_err());
	/// drop(clone);
	///
	/// let weak = deque.demote();
	/// assert!(deque.unique().is_err());
	/// ```
	pub fn unique(&mut self) -> Result<Unique<T, A, ATOMIC>> {
		todo!()
	}

	/// Reserves space for at least `additional` elements. The deque may reserve more space to
	/// speculatively avoid frequent reallocations. The reserved capacity will be greater than or
	/// equal to `length + additional`. No memory is allocated if the capacity is already sufficient.
	///
	/// Where the element type implements [`Clone`], [`reserve`] can be used to clone out of shared
	/// allocations.
	///
	/// [`reserve`]: Self::reserve
	///
	/// # Errors
	///
	/// Returns an error if the allocation would grow, but cannot be resized because it holds a
	/// shared reference to its allocation.
	///
	/// # Panics
	///
	/// Panics if the new capacity is greater than [`isize::MAX`] *bytes* minus four [`usize`]
	/// words.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque: Deque<i32> = Deque::from([1]);
	/// assert_eq!(deque.try_reserve(10), Ok(()));
	/// assert!(deque.capacity() >= 11);
	/// ```
	pub fn try_reserve(&mut self, additional: usize) -> Result {
		todo!()
	}

	/// Reserves the minimum space for at least `additional` elements, without speculative
	/// over-allocation [`try_reserve`] and [`reserve`] do. The reserved will be greater than or
	/// equal to `length + additional`. No memory is allocated if the capacity is already sufficient.
	///
	/// The allocator may give the deque more space than it requests. Therefore, capacity cannot be
	/// relied upon to be precisely minimal. [`try_reserve`] is preferred if future insertions are
	/// expected.
	///
	/// Where the element type implements [`Clone`], [`reserve_exact`] can be used to clone out of
	/// shared allocations.
	///
	/// [`try_reserve`]: Self::try_reserve
	/// [`reserve`]: Self::reserve
	/// [`reserve_exact`]: Self::reserve_exact
	///
	/// # Errors
	///
	/// Returns an error if the allocation would grow, but cannot be resized because it holds a
	/// shared reference to its allocation.
	///
	/// # Panics
	///
	/// Panics if the new capacity is greater than [`isize::MAX`] *bytes* minus four [`usize`]
	/// words.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque: Deque<i32> = Deque::from([1]);
	/// assert_eq!(deque.try_reserve_exact(10), Ok(()));
	/// assert!(deque.capacity() >= 11);
	/// ```
	pub fn try_reserve_exact(&mut self, additional: usize) -> Result {
		todo!()
	}

	// Todo: try_reserve with errors instead of panics, similar to VecDeque::try_reserve?

	/// Shrinks the capacity of the deque as much as possible.
	///
	/// The behavior of this method depends on the allocator, which may either shrink the deque
	/// in-place or reallocate. The resulting deque might still have some excess capacity, just as
	/// is the case for [`with_capacity`]. See [`Allocator::shrink`] for more details.
	///
	/// Where the element type implements [`Clone`], [`shrink_to_fit`] can be used to clone out of
	/// shared allocations.
	///
	/// [`with_capacity`]: Self::with_capacity
	/// [`shrink_to_fit`]: Self::shrink_to_fit
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque: Deque<i32> = Deque::with_capacity(10);
	/// deque.extend([1, 2, 3]);
	/// assert!(deque.capacity() >= 10);
	/// assert_eq!(deque.try_shrink_to_fit(), Ok(()));
	/// assert!(deque.capacity() >= 3);
	/// ```
	pub fn try_shrink_to_fit(&mut self) -> Result {
		todo!()
	}

	/// Shrinks the capacity of the deque with a lower bound.
	///
	/// The capacity will be at least as large as both the length and the supplied value. If the
	/// current capacity is less than the lower limit, this does nothing.
	///
	/// Where the element type implements [`Clone`], [`shrink_to`] can be used to clone out of
	/// shared allocations.
	///
	/// [`shrink_to`]: Self::shrink_to
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque: Deque<i32> = Deque::with_capacity(10);
	/// deque.extend([1, 2, 3]);
	/// assert!(deque.capacity() >= 10);
	/// assert_eq!(deque.try_shrink_to(4), Ok(()));
	/// assert!(deque.capacity() >= 4);
	/// assert_eq!(deque.try_shrink_to(0), Ok(()));
	/// assert!(deque.capacity() >= 3);
	/// ```
	pub fn try_shrink_to(&mut self, min_capacity: usize) -> Result {
		todo!()
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
	/// use sharevec::deque::rc::Deque;
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
	/// let mut deque1 = Deque::from([
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
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque: Deque<i32> = Deque::from([1, 2, 3, 4, 5]);
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
	/// use sharevec::deque::rc::Deque;
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
	/// let mut deque1 = Deque::from([
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
	/// deque1.try_push_back(WithDrop { val: 3 }).unwrap();
	/// // Output:
	/// // Dropping 3
	/// deque1.clear();
	/// ```
	///
	/// [`unique`]: Self::unique
	/// [`as_unique`]: Self::as_unique
	/// [`is_unique`]: Self::is_unique
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque: Deque<i32> = Deque::from([1, 2, 3]);
	/// deque.clear();
	///
	/// assert_eq!(deque, []);
	/// ```
	pub fn clear(&mut self) {
		todo!()
	}

	/// Returns the number of elements in the deque.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let deque = Deque::from([1, 2, 3]);
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
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque: Deque<i32> = Deque::new();
	/// assert!(!deque.is_not_empty());
	///
	/// deque.push_back(1);
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
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque: Deque<i32> = Deque::new();
	/// assert!(!deque.is_not_empty());
	///
	/// deque.push_back(1);
	/// assert!(deque.is_not_empty());
	/// ```
	pub fn is_not_empty(&self) -> bool {
		!self.is_empty()
	}
	/// Returns `true` if the deque cannot hold any more elements without resizing.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque = Deque::from([1, 2, 3]);
	/// assert!(deque.is_full());
	///
	/// deque.pop_back();
	/// assert!(!deque.is_full());
	/// ```
	pub fn is_full(&self) -> bool {
		self.len() == self.capacity()
	}
	/// Returns `true` if the deque can hold more elements without resizing.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque = Deque::from([1, 2, 3]);
	/// assert!(!deque.is_not_full());
	///
	/// deque.pop_back();
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
	/// use sharevec::deque::rc::Deque;
	///
	/// let deque = Deque::from([1, 2, 3]);
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
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque = Deque::from([1, 2, 3]);
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
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque = Deque::from([1, 2, 3]);
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
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque = Deque::from([1, 2, 3]);
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
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque = Deque::from([1, 2, 3]);
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
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque = Deque::from([1, 2, 3]);
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
	/// use sharevec::deque::arc::Deque;
	///
	/// let mut deque: Deque<i32> = Deque::from([0, 1]);
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

	/// Returns an iterator returning references to elements front-to-back.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let deque: Deque<i32> = Deque::from([1, 2, 3]);
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
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque: Deque<i32> = Deque::from([1, 2, 3]);
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
	/// use sharevec::deque::rc::Deque;
	///
	/// let deque = Deque::from([1, 2, 3]);
	/// let range = deque.range(2..).copied().collect::<Deque<_>>();
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
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque = Deque::from([1, 2, 3]);
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
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque = Deque::from([1, 2]);
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
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque = Deque::from([1, 2]);
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
	/// Returns an error containing the `value` if the deque holds a shared reference to its buffer.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::error::Shared;
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque = Deque::new();
	/// assert_eq!(deque.try_push_front(1), Ok(()));
	/// assert_eq!(deque.try_push_front(2), Ok(()));
	/// assert_eq!(deque, [2, 1]);
	///
	/// let clone = deque.clone();
	/// assert_eq!(deque.try_push_front(3), Err(Shared(3)));
	/// assert_eq!(deque.len(), 2);
	/// ```
	pub fn try_push_front(&mut self, value: T) -> Result<(), Shared<T>> {
		todo!()
	}
	/// Appends an element to the back of the deque.
	///
	/// # Errors
	///
	/// Returns an error containing the `value` if the deque holds a shared reference to its buffer.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::error::Shared;
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque = Deque::new();
	/// assert_eq!(deque.try_push_back(1), Ok(()));
	/// assert_eq!(deque.try_push_back(2), Ok(()));
	/// assert_eq!(deque, [1, 2]);
	///
	/// let clone = deque.clone();
	/// assert_eq!(deque.try_push_back(3), Err(Shared(3)));
	/// assert_eq!(deque.len(), 2);
	/// ```
	pub fn try_push_back(&mut self, value: T) -> Result<(), Shared<T>> {
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
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut buf = Deque::from([1, 2, 3]);
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
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque = Deque::from([1, 2, 3]);
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
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque = Deque::from([1, 2, 3]);
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
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque = Deque::from([1, 2, 3]);
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
	/// Returns an error containing the element if the deque is immutable because it holds a shared
	/// reference to its buffer.
	///
	/// # Panics
	///
	/// Panics if `index` is greater than the deque length.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque = Deque::new();
	/// assert_eq!(deque.try_push_back(1), Ok(()));
	/// assert_eq!(deque.try_push_back(3), Ok(()));
	/// assert_eq!(deque.try_push_back(4), Ok(()));
	/// assert_eq!(deque, [1, 3, 4]);
	///
	/// assert_eq!(deque.try_insert(1, 2), Ok(()));
	/// assert_eq!(deque, [1, 2, 3, 4]);
	/// ```
	pub fn try_insert(&mut self, index: usize, element: T) -> Result<(), Shared<T>> {
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
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque: Deque<i32> = Deque::from([1, 2, 3, 4]);
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
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque: Deque<i32> = Deque::from([1, 2, 3, 4]);
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
	/// Moves all elements from `other` into this deque, leaving `other` empty. Any like[^atomic]
	/// vector/deque type from this crate may be appended, even array vectors/deques with a different
	/// fixed capacity.
	///
	/// [^atomic]: the only restriction is that both vectors/deques must either be atomic or
	/// non-atomic; atomic vectors/deques may be only appended to other atomic vectors/deques,
	/// non-atomic vectors/deques may only be appended to other non-atomic vectors/deques.
	///
	/// # Errors
	///
	/// Returns an error if either of the vectors are immutable because they hold a shared reference
	/// to their respective buffers. In this case, neither vector/deque is modified.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque1: Deque<i32> = Deque::from([1, 2, 3]);
	/// let mut deque2 = Deque::from([4, 5, 6]);
	/// assert_eq!(deque1.try_append(&mut deque2), Ok(()));
	/// assert_eq!(deque1, [1, 2, 3, 4, 5, 6]);
	/// assert_eq!(deque2, []);
	/// ```
	pub fn try_append<V: RcVector<T, A, ATOMIC> + ?Sized>(&mut self, other: &mut V) -> Result {
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
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque: Deque<i32> = Deque::from([1, 2, 3, 4, 5, 6, 7, 8]);
	/// let removed = deque.try_drain(2..6).map(Iterator::collect::<Deque<_>>);
	/// assert_eq!(removed, Ok([3, 4, 5, 6].into()));
	/// assert_eq!(deque, [1, 2, 7, 8]);
	/// ```
	pub fn try_drain<R: RangeBounds<usize>>(&mut self, range: R) -> Result<Drain<T, A, ATOMIC>> {
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
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque = Deque::from([1, 2, 3, 4]);
	/// assert_eq!(deque.try_split_off(2), Ok([3, 4].into()));
	/// assert_eq!(deque, [1, 2]);
	/// ```
	pub fn try_split_off(&mut self, at: usize) -> Result<Self>
	where A: Clone {
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
	/// Returns an error if the deque is immutable because it holds a shared reference to its buffer.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque: Deque<i32> = Deque::from([1, 2, 3]);
	/// let fill = Default::default;
	///
	/// assert_eq!(deque.try_resize_with(5, fill), Ok(()));
	/// assert_eq!(deque, [1, 2, 3, 0, 0]);
	/// assert_eq!(deque.try_resize_with(3, fill), Ok(()));
	/// assert_eq!(deque, [1, 2, 3]);
	/// ```
	pub fn try_resize_with<F: FnMut() -> T>(&mut self, new_len: usize, fill: F) -> Result {
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
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque: Deque<i32> = Deque::with_capacity(3);
	///
	/// deque.push_back(2);
	/// deque.push_back(1);
	/// deque.push_front(3);
	/// assert_eq!(deque.as_slices(), (&[2, 1][..], &[3][..]));
	///
	/// deque.try_make_contiguous().unwrap();
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
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque: Deque<i32> = (0..10).collect();
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
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque: Deque<i32> = (0..10).collect();
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
	/// use sharevec::deque::rc::Deque;
	///
	/// let deque = Deque::from([0, 1, 1, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55]);
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
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque = Deque::from([0, 1, 1, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55]);
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
	/// use sharevec::deque::rc::Deque;
	///
	/// let deque = Deque::from([0, 1, 1, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55]);
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
	/// use sharevec::deque::rc::Deque;
	///
	/// let deque = Deque::from([
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
	/// use sharevec::deque::rc::Deque;
	///
	/// let deque = Deque::from([1, 2, 3, 3, 5, 6, 7]);
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
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque = Deque::from([0, 1, 1, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55]);
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
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque: Deque<i32> = Deque::from([1, 2, 3]);
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
	/// Returns an error if the deque is immutable because it holds a shared reference to its
	/// buffer.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque: Deque<i32> = Deque::new();
	/// assert_eq!(deque.try_extend([1, 2]), Ok(()));
	/// assert_eq!(deque, [1, 2]);
	/// ```
	pub fn try_extend<I: IntoIterator<Item = T>>(&mut self, iter: I) -> Result<(), Shared<I>> {
		todo!()
	}
	/// Appends referenced elements from an iterator to the back of the deque by copying.
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
	/// let mut deque: ArrayDeque<i32, 3> = ArrayDeque::new();
	/// assert_eq!(deque.try_extend_ref(&[1, 2]), Ok(()));
	/// assert_eq!(deque, [1, 2]);
	/// ```
	pub fn try_extend_ref<'a, I: IntoIterator<Item = &'a T>>(&mut self, iter: I) -> Result<(), Shared<I>>
	where T: Copy + 'a {
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
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque: Deque<i32> = Deque::from([1, 2, 3]);
	/// let mut iter = deque.try_into_iter().unwrap();
	/// assert!(iter.eq([1, 2, 3]));
	/// ```
	pub fn try_into_iter(self) -> Result<IntoIter<T, A, ATOMIC>, Self> {
		todo!()
	}

	/// Converts the fixed-capacity deque into a variable-capacity deque of capacity `N`.
	///
	/// This may be done even when the vector is shared. This operation takes *O*(1) time, and does
	/// not allocate memory.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::TryInsert;
	/// use sharevec::deque::rc::Deque;
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let array_deque: Deque<i32> = Deque::from([1, 2, 3]);
	/// let mut deque: ArrayDeque<i32, 3> = array_deque.into_array_deque().unwrap();
	/// assert_eq!(deque.capacity(), 3);
	/// // The vector now can't grow its capacity beyond the fixed capacity.
	/// assert_eq!(deque.try_push_back(4), Err(TryInsert::FullCapacity { element: 4 }));
	/// ```
	#[cfg(feature = "array-deque")]
	pub fn into_array_deque<const N: usize>(self) -> Result<ArrayDeque<T, N, ATOMIC, A>, Self> {
		todo!()
	}
}

impl<T: Clone, A: Allocator, const ATOMIC: bool> Deque<T, ATOMIC, A> {
	/// Resizes the deque in-place to the specified length, cloning `value` into additional space as
	/// needed.
	///
	/// If `new_len` is greater than the current length, the deque is extended, filling the
	/// additional space with `value`. If `new_len` is less than the current length, the deque is
	/// truncated.
	///
	/// # Leaking
	///
	/// If the vector is truncated, the same leaking caveats as [`truncate`] apply.
	///
	/// [`truncate`]: Self::truncate#leaking
	///
	/// # Errors
	///
	/// Returns an error if the deque is immutable because it holds a shared reference to its buffer.
	/// In this case, the vector is filled completely.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque: Deque<i32> = Deque::from([1, 2, 3]);
	///
	/// assert_eq!(deque.try_resize(5, 0), Ok(()));
	/// assert_eq!(deque, [1, 2, 3, 0, 0]);
	/// assert_eq!(deque.try_resize(3, 0), Ok(()));
	/// assert_eq!(deque, [1, 2, 3]);
	/// ```
	pub fn try_resize(&mut self, new_len: usize, value: T) -> Result {
		todo!()
	}

	/// Clones and appends all elements in a slice to the back of the deque.
	///
	/// # Errors
	///
	/// Returns an error if the deque is immutable because it holds a shared reference to its buffer.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque: Deque<i32> = Deque::new();
	/// assert_eq!(deque.try_extend_from_slice(&[1, 2, 3]), Ok(()));
	/// ```
	pub fn try_extend_from_slice(&mut self, other: &[T]) -> Result {
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
	/// Returns an error if the deque is immutable because it holds a shared reference to its buffer.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque: Deque<i32> = Deque::from([1, 2, 3, 4]);
	/// assert_eq!(deque.try_extend_from_within(1..3), Ok(()));
	/// assert_eq!(deque, [1, 2, 3, 4, 2, 3]);
	/// ```
	pub fn try_extend_from_within<R: RangeBounds<usize>>(&mut self, range: R) -> Result<> {
		todo!()
	}
}

// CoW operations
impl<T: Clone, A: Allocator + Clone, const ATOMIC: bool> Deque<T, ATOMIC, A> {
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
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque = Deque::with_capacity(4);
	/// deque.push_back(0);
	/// deque.push_back(1);
	///
	/// deque.push_front(10);
	/// deque.push_front(9);
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
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque: Deque<i32> = Deque::from([1, 2, 3]);
	/// let clone = deque.clone();
	///
	/// let mut unique = deque.as_unique();
	/// unique.clear();
	/// unique.extend_from_slice(&[4, 5, 6]);
	/// assert!(deque.is_unique());
	/// assert_eq!(deque, [4, 5, 6]);
	///
	/// // The first deque's contents have been cloned and are no longer shared
	/// // with the second.
	/// assert!(clone.is_unique());
	/// assert_ne!(deque, clone);
	/// ```
	pub fn as_unique(&mut self) -> Unique<T, A, ATOMIC> {
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
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque: Deque<i32> = Deque::from([1, 2, 3]);
	/// let clone = deque.clone();
	///
	/// let mut unique = deque.try_as_unique().expect("allocation failed");
	/// unique.clear();
	/// unique.extend_from_slice(&[4, 5, 6]);
	/// assert!(deque.is_unique());
	/// assert_eq!(deque, [4, 5, 6]);
	///
	/// // The first deque's contents have been cloned and are no longer shared
	/// // with the second.
	/// assert!(clone.is_unique());
	/// assert_ne!(deque, clone);
	/// ```
	pub fn try_as_unique(&mut self) -> Result<Unique<T, A, ATOMIC>, AllocError> {
		todo!()
	}

	/// Reserves space for at least `additional` elements, cloning out of a shared reference. The
	/// deque may reserve more space to speculatively avoid frequent reallocations. The reserved
	/// capacity will be greater than or equal to `length + additional`. No memory is allocated if
	/// the capacity is already sufficient.
	///
	/// To return an error if the deque is shared without cloning, use [`try_reserve`] instead.
	///
	/// [`try_reserve`]: Self::try_reserve
	///
	/// # Panics
	///
	/// Panics if the new capacity is greater than [`isize::MAX`] *bytes* minus four [`usize`]
	/// words.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque: Deque<i32> = Deque::from([1]);
	/// deque.reserve(10);
	/// assert!(deque.capacity() >= 11);
	/// ```
	pub fn reserve(&mut self, additional: usize) {
		todo!()
	}

	/// Reserves the minimum space for at least `additional` elements, without speculative
	/// over-allocation [`try_reserve`] and [`reserve`] do. The reserved will be greater than or
	/// equal to `length + additional`. No memory is allocated if the capacity is already sufficient.
	///
	/// This clones out of a shared reference.
	///
	/// The allocator may give the deque more space than it requests. Therefore, capacity cannot be
	/// relied upon to be precisely minimal. [`reserve`] is preferred if future insertions are
	/// expected.
	///
	/// To return an error if the deque is shared without cloning, use [`try_reserve_exact`]
	/// instead.
	///
	/// [`try_reserve`]: Self::try_reserve
	/// [`reserve`]: Self::reserve
	/// [`reserve_exact`]: Self::reserve_exact
	///
	/// # Panics
	///
	/// Panics if the new capacity is greater than [`isize::MAX`] *bytes* minus four [`usize`]
	/// words.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque: Deque<i32> = Deque::from([1]);
	/// deque.reserve_exact(10);
	/// assert!(deque.capacity() >= 11);
	/// ```
	pub fn reserve_exact(&mut self, additional: usize) {
		todo!()
	}

	// Todo: try_reserve with errors instead of panics, similar to VecDeque::try_reserve?

	/// Shrinks the capacity of the deque as much as possible, cloning out of a shared reference.
	///
	/// The behavior of this method depends on the allocator, which may either shrink the vector
	/// in-place or reallocate. The resulting deque might still have some excess capacity, just as
	/// is the case for [`with_capacity`]. See [`Allocator::shrink`] for more details.
	///
	/// To return an error if the deque is shared without cloning, use [`try_shrink_to_fit`]
	/// instead.
	///
	/// [`with_capacity`]: Self::with_capacity
	/// [`try_shrink_to_fit`]: Self::try_shrink_to_fit
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque: Deque<i32> = Deque::with_capacity(10);
	/// deque.extend([1, 2, 3]);
	/// assert!(deque.capacity() >= 10);
	/// deque.shrink_to_fit();
	/// assert!(deque.capacity() >= 3);
	/// ```
	pub fn shrink_to_fit(&mut self) {
		todo!()
	}

	/// Shrinks the capacity of the deque with a lower bound.
	///
	/// The capacity will be at least as large as both the length and the supplied value. If the
	/// current capacity is less than the lower limit, this does nothing.
	///
	/// To return an error if the deque is shared without cloning, use [`try_shrink_to`] instead.
	///
	/// [`try_shrink_to`]: Self::try_shrink_to
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque: Deque<i32> = Deque::with_capacity(10);
	/// deque.extend([1, 2, 3]);
	/// assert!(deque.capacity() >= 10);
	/// deque.shrink_to(4);
	/// assert!(deque.capacity() >= 4);
	/// deque.shrink_to(0);
	/// assert!(deque.capacity() >= 3);
	/// ```
	pub fn shrink_to(&mut self, min_capacity: usize) {
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
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque = Deque::from([1, 2, 3]);
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
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque = Deque::from([1, 2, 3]);
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
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque = Deque::from([1, 2, 3]);
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
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque: Deque<i32> = Deque::from([1, 2, 3]);
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
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque = Deque::from([1, 2, 3]);
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
	/// # Panics
	///
	/// Panics if allocation fails, for example in an out-of-memory condition.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque = Deque::new();
	/// deque.push_front(1);
	/// deque.push_front(2);
	/// assert_eq!(deque, [2, 1]);
	/// ```
	pub fn push_front(&mut self, value: T) {
		todo!()
	}
	/// Appends an element to the back of the deque.
	///
	/// If the deque is shared and has spare capacity, its contents are cloned. A fallible version
	/// is also provided: [`try_push_back`].
	///
	/// [`try_push_back`]: Self::try_push_back
	///
	/// # Panics
	///
	/// Panics if allocation fails, for example in an out-of-memory condition.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque = Deque::new();
	/// deque.push_back(1);
	/// deque.push_back(2);
	/// assert_eq!(deque, [1, 2]);
	/// ```
	pub fn push_back(&mut self, value: T) {
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
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut buf = Deque::from([1, 2, 3]);
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
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque = Deque::from([1, 2, 3]);
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
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque = Deque::from([1, 2, 3]);
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
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque = Deque::from([1, 2, 3]);
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
	/// # Panics
	///
	/// Panics if:
	/// - allocation fails, for example in an out-of-memory condition
	/// - `index` is greater than the vector length
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque: Deque<i32> = Deque::from([1, 3, 4]);
	///
	/// deque.insert(1, 2);
	/// assert_eq!(deque, [1, 2, 3, 4]);
	/// ```
	pub fn insert(&mut self, index: usize, element: T) {
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
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque: Deque<i32> = Deque::from([1, 2, 3, 4]);
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
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque: Deque<i32> = Deque::from([1, 2, 3, 4]);
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
	/// If one vector is shared, it is effectively [`clear`]ed, causing all its elements to go out
	/// of scope without dropping. The elements' [`Drop`] implementation can only be safely called
	/// when both vectors hold a unique reference.
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
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque1: Deque<i32> = Deque::from([1, 2, 3]);
	/// let mut deque2 = Deque::from([4, 5, 6]);
	/// deque1.append(&mut deque2);
	/// assert_eq!(deque1, [1, 2, 3, 4, 5, 6]);
	/// assert_eq!(deque2, []);
	/// ```
	pub fn append<V: RcVector<T, A, ATOMIC> + ?Sized>(&mut self, other: &mut V) {
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
	/// example), the vector may have lost and leaked elements arbitrarily, including elements outside
	/// the range.
	///
	/// [`forget`]: core::mem::forget
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque: Deque<i32> = Deque::from([1, 2, 3, 4, 5, 6, 7, 8]);
	/// let removed = deque.drain(2..6);
	/// assert!(removed.eq([3, 4, 5, 6]));
	/// assert_eq!(deque, [1, 2, 7, 8]);
	/// ```
	pub fn drain<R: RangeBounds<usize>>(&mut self, range: R) -> Drain<T, A, ATOMIC> {
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
	/// - `at` is greater than the vector length
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque = Deque::from([1, 2, 3, 4]);
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
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque: Deque<i32> = Deque::from([1, 2, 3]);
	/// let fill = Default::default;
	///
	/// deque.resize_with(5, fill);
	/// assert_eq!(deque, [1, 2, 3, 0, 0]);
	/// deque.resize_with(3, fill);
	/// assert_eq!(deque, [1, 2, 3]);
	/// ```
	pub fn resize_with<F: FnMut() -> T>(&mut self, new_len: usize, fill: F) {
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
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque: Deque<i32> = Deque::from([1, 2, 3]);
	///
	/// deque.resize(5, 0);
	/// assert_eq!(deque, [1, 2, 3, 0, 0]);
	/// deque.resize(3, 0);
	/// assert_eq!(deque, [1, 2, 3]);
	/// ```
	pub fn resize(&mut self, new_len: usize, value: T) {
		todo!()
	}

	/// Rearranges the contents of the deque such that they are stored in a single contiguous slice,
	/// returning the slice. The order of the elements in the deque is preserved; only the internal
	/// storage is changed.
	///
	/// Once the internal storage is contiguous, the [`as_slices`] and [`as_mut_slices`] will return the
	/// entire contents of the deque in a single slice.
	///
	/// If the deque is shared but must be rearranged, its contents are cloned. A fallible version
	/// is also provided: [`try_make_contiguous`].
	///
	/// [`as_slices`]: Self::as_slices
	/// [`as_mut_slices`]: Self::as_mut_slices
	/// [`try_make_contiguous`]: Self::try_make_contiguous
	///
	/// # Panics
	///
	/// Panics if allocation fails, for example in an out-of-memory condition.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque: Deque<i32> = Deque::with_capacity(3);
	///
	/// deque.push_back(2);
	/// deque.push_back(1);
	/// deque.push_front(3);
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
	/// use sharevec::deque::arc::Deque;
	///
	/// let mut deque: Deque<i32> = (0..10).collect();
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
	/// use sharevec::deque::arc::Deque;
	///
	/// let mut deque: Deque<i32> = (0..10).collect();
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
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque: Deque<i32> = Deque::new();
	/// deque.extend_from_slice(&[1, 2, 3]);
	/// assert_eq!(deque, [1, 2, 3]);
	/// ```
	pub fn extend_from_slice(&mut self, other: &[T]) {
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
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque: Deque<i32> = Deque::from([1, 2, 3, 4]);
	/// deque.extend_from_within(1..3);
	/// assert_eq!(deque, [1, 2, 3, 4, 2, 3]);
	/// ```
	pub fn extend_from_within<R: RangeBounds<usize>>(&mut self, range: R) {
		todo!()
	}
}

impl<T: Clone, A: Allocator, const ATOMIC: bool> Deque<T, ATOMIC, A> {
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
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque = Deque::from([1, 2]);
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
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque = Deque::from([1, 2]);
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

impl<T, A: Allocator + Clone, const ATOMIC: bool> Clone for Deque<T, ATOMIC, A> {
	/// Creates a new deque sharing its contents with this deque.
	///
	/// If the fixed capacity is `0`, both deques remain unique.
	fn clone(&self) -> Self {
		todo!()
	}
}

impl<T: Hash, A: Allocator, const ATOMIC: bool> Hash for Deque<T, ATOMIC, A> {
	fn hash<H: Hasher>(&self, state: &mut H) {
		// Todo: use write_length_prefix when stable
		state.write_usize(self.len());
		for v in self.iter() {
			Hash::hash(v, state);
		}
	}
}

impl<T, A: Allocator, const ATOMIC: bool> Index<usize> for Deque<T, ATOMIC, A> {
	type Output = T;

	fn index(&self, index: usize) -> &Self::Output {
		self.get(index).expect("Out of bounds access")
	}
}

impl<T, const ATOMIC: bool> FromIterator<T> for Deque<T, ATOMIC> {
	fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
		todo!()
	}
}

impl<T: Clone, A: Allocator, const ATOMIC: bool> IntoIterator for Deque<T, ATOMIC, A> {
	type Item = T;
	type IntoIter = IntoIter<T, A, ATOMIC>;

	/// Consumes the deque into a front-to-back iterator yielding elements by value. If the deque is
	/// shared, the elements are cloned out of the deque.
	fn into_iter(self) -> Self::IntoIter {
		todo!()
	}
}

impl<'a, T, A: Allocator, const ATOMIC: bool> IntoIterator for &'a Deque<T, ATOMIC, A> {
	type Item = &'a T;
	type IntoIter = Iter<'a, T>;

	fn into_iter(self) -> Self::IntoIter {
		self.iter()
	}
}

impl<T: Clone, A: Allocator + Clone, const ATOMIC: bool> Extend<T> for Deque<T, ATOMIC, A> {
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

impl<'a, T: Copy + 'a, A: Allocator + Clone, const ATOMIC: bool> Extend<&'a T> for Deque<T, ATOMIC, A> {
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

impl<T: Eq, A: Allocator, const ATOMIC: bool> Eq for Deque<T, ATOMIC, A> { }

impl<T, A1, A2, const ATOMIC1: bool, const ATOMIC2: bool> PartialOrd<Deque<T, ATOMIC2, A2>> for Deque<T, ATOMIC1, A1>
where
	T: PartialOrd,
	A1: Allocator,
	A2: Allocator
{
	fn partial_cmp(&self, other: &Deque<T, ATOMIC2, A2>) -> Option<Ordering> {
		todo!()
	}
}

impl<T: Ord, A: Allocator, const ATOMIC: bool> Ord for Deque<T, ATOMIC, A> {
	fn cmp(&self, other: &Self) -> Ordering {
		todo!()
	}
}

impl<T, A: Allocator, const ATOMIC: bool> Drop for Deque<T, ATOMIC, A> {
	fn drop(&mut self) {
		todo!()
	}
}

impl<T, const ATOMIC: bool> Default for Deque<T, ATOMIC> {
	fn default() -> Self {
		Self::new()
	}
}

impl<T: fmt::Debug, A: Allocator, const ATOMIC: bool> fmt::Debug for Deque<T, ATOMIC, A> {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		todo!()
	}
}

// Contiguous collection conversions

impl<T, A: Allocator, const ATOMIC: bool> From<Vec<T, ATOMIC, A>> for Deque<T, ATOMIC, A> {
	/// Converts a [`Vec`] into a [`Deque`].
	fn from(value: Vec<T, ATOMIC, A>) -> Self {
		todo!()
	}
}

impl<T, A: Allocator, const ATOMIC: bool> TryFrom<Deque<T, ATOMIC, A>> for Vec<T, ATOMIC, A> {
	type Error = Shared<Deque<T, ATOMIC, A>>;

	/// Converts a [`Deque`] into a [`Vec`].
	///
	/// # Errors
	///
	/// Returns an error containing the deque if it is not contiguous and holds a shared reference.
	fn try_from(mut value: Deque<T, ATOMIC, A>) -> Result<Self, Self::Error> {
		let Ok(_) = value.try_make_contiguous() else { return Err(Shared(value)) };
		todo!()
	}
}

impl<T, const N: usize, A: Allocator, const ATOMIC: bool> From<ArrayVec<T, N, ATOMIC, A>> for Deque<T, ATOMIC, A> {
	/// Converts a fixed-capacity vector into a variable-capacity deque of capacity `N`.
	fn from(value: ArrayVec<T, N, ATOMIC, A>) -> Self {
		todo!()
	}
}

pub enum TryIntoArrayVec<T> {
	Discontiguous(T),
	Resize(T)
}

impl<T> From<Shared<T>> for TryIntoArrayVec<T> {
	fn from(Shared(v): Shared<T>) -> Self {
		Self::Discontiguous(v)
	}
}

impl<T, const N: usize, A: Allocator, const ATOMIC: bool> TryFrom<Deque<T, ATOMIC, A>> for ArrayVec<T, N, ATOMIC, A> {
	type Error = TryIntoArrayVec<Deque<T, ATOMIC, A>>;

	/// Converts a variable-capacity deque into a fixed-capacity vector of capacity `N`.
	///
	/// # Errors
	///
	/// If the deque holds a shared reference, returns:
	/// - [`Discontiguous`] if the deque is not contiguous
	/// - [`Resize`] if the deque must resize
	///
	/// [`Discontiguous`]: TryIntoArrayVec::Discontiguous
	/// [`Resize`]: TryIntoArrayVec::Resize
	fn try_from(value: Deque<T, ATOMIC, A>) -> Result<Self, Self::Error> {
		let array_deque = match value.into_array_deque() {
			Ok(d) => d,
			Err(e) => return Err(TryIntoArrayVec::Resize(e))
		};
		let array_vec = match ArrayVec::try_from(array_deque) {
			Ok(v) => v,
			Err(Shared(e)) => return Err(TryIntoArrayVec::Discontiguous(e.into_deque()))
		};

		Ok(array_vec)
	}
}

// Array and slice conversions

impl<T: Clone, const N: usize, const ATOMIC: bool> From<&[T; N]> for Deque<T, ATOMIC> {
	fn from(value: &[T; N]) -> Self {
		todo!()
	}
}

impl<T: Clone, const N: usize, const ATOMIC: bool> From<&mut [T; N]> for Deque<T, ATOMIC> {
	fn from(value: &mut [T; N]) -> Self {
		todo!()
	}
}

impl<T, const N: usize, const ATOMIC: bool> From<[T; N]> for Deque<T, ATOMIC> {
	fn from(value: [T; N]) -> Self {
		todo!()
	}
}

impl<T: Clone, const N: usize, A: Allocator, const ATOMIC: bool> TryFrom<Deque<T, ATOMIC, A>> for [T; N] {
	type Error = Deque<T, ATOMIC, A>;

	/// Converts a [`Deque`] into an array, cloning out of a shared allocation.
	///
	/// # Errors
	///
	/// Returns the vector back if its length is too large or small to fit in the array size.
	fn try_from(value: Deque<T, ATOMIC, A>) -> Result<Self, Self::Error> {
		todo!()
	}
}

impl<T: Clone, const ATOMIC: bool> From<&[T]> for Deque<T, ATOMIC> {
	fn from(value: &[T]) -> Self {
		todo!()
	}
}

impl<T: Clone, const ATOMIC: bool> From<&mut [T]> for Deque<T, ATOMIC> {
	fn from(value: &mut [T]) -> Self {
		todo!()
	}
}

impl<const ATOMIC: bool> From<&str> for Deque<u8, ATOMIC> {
	fn from(value: &str) -> Self {
		value.as_bytes().into()
	}
}

// Fallible Box/Vec conversions

impl<T, A: Allocator, const ATOMIC: bool> From<StdVec<T, A>> for Deque<T, ATOMIC, A> {
	/// Converts a [`Vec`] into a reference-counted, fixed-capacity deque.
	///
	/// [`Vec`]: alloc::vec::Vec
	///
	/// # Panics
	///
	/// Panics if allocation fails, for example in an out-of-memory condition.
	fn from(value: StdVec<T, A>) -> Self {
		todo!()
	}
}

impl<T, A: Allocator, const ATOMIC: bool> TryFrom<Deque<T, ATOMIC, A>> for StdVec<T, A> {
	type Error = Shared<Deque<T, ATOMIC, A>>;

	/// Converts a reference-counted, fixed-capacity deque of capacity `N` into a [`Vec`].
	///
	/// [`Vec`]: alloc::vec::Vec
	///
	/// # Errors
	///
	/// Returns an error containing the deque if it is not contiguous and holds a shared reference.
	///
	/// # Panics
	///
	/// Panics if allocation fails, for example in an out-of-memory condition.
	fn try_from(value: Deque<T, ATOMIC, A>) -> Result<Self, Self::Error> {
		todo!()
	}
}

impl<T, A: Allocator, const ATOMIC: bool> From<VecDeque<T, A>> for Deque<T, ATOMIC, A> {
	/// Converts a [`VecDeque`] into a reference-counted, fixed-capacity deque.
	///
	/// # Panics
	///
	/// Panics if allocation fails, for example in an out-of-memory condition.
	fn from(value: VecDeque<T, A>) -> Self {
		todo!()
	}
}

impl<T, A: Allocator, const ATOMIC: bool> TryFrom<Deque<T, ATOMIC, A>> for VecDeque<T, A> {
	type Error = Shared<Deque<T, ATOMIC, A>>;

	/// Converts a reference-counted, fixed-capacity deque of capacity `N` into a [`VecDeque`].
	///
	/// # Errors
	///
	/// Returns an error containing the deque if it holds a shared reference.
	///
	/// # Panics
	///
	/// Panics if allocation fails, for example in an out-of-memory condition.
	fn try_from(value: Deque<T, ATOMIC, A>) -> Result<Self, Self::Error> {
		todo!()
	}
}

impl<const ATOMIC: bool> From<String> for Deque<u8, ATOMIC> {
	fn from(value: String) -> Self {
		value.into_bytes().into()
	}
}

impl<T, A: Allocator, const ATOMIC: bool> From<Box<[T], A>> for Deque<T, ATOMIC, A> {
	fn from(value: Box<[T], A>) -> Self {
		todo!()
	}
}

impl<T, A: Allocator, const N: usize, const ATOMIC: bool> From<Box<[T; N], A>> for Deque<T, ATOMIC, A> {
	fn from(value: Box<[T; N], A>) -> Self {
		todo!()
	}
}

impl<A: Allocator, const ATOMIC: bool> From<Box<str, A>> for Deque<u8, ATOMIC, A> {
	fn from(value: Box<str, A>) -> Self {
		Box::<[u8], A>::from(value).into()
	}
}
