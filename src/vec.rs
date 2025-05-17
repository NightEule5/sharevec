// Copyright 2024 - Strixpyrr
// SPDX-License-Identifier: Apache-2.0

//! # Uniqueness
//!
//! Vectors access or modify their contents through an *allocation reference*, which may be shared by
//! other vectors. Vectors hold a *strong* reference to their allocated capacity. If only one vector
//! holds a strong allocation reference, it is called *strongly unique*, allowing it to be modified.
//! Multiple vectors may *strongly share* the same referenced allocation, making them all immutable.
//! To modify a shared vector, its contents must first be cloned to a unique allocation.
//!
//! As with [`Rc`], a vector may be downgraded into a *weak* reference, which does not prevent
//! modifying but does prevent de/reallocation. If there are any weak references to a vector's
//! capacity, the vector is called *weakly shared*. This forces strongly unique vectors to clone
//! their contents to grow or shrink their capacity, instead of resizing in-place.
//!
//! # Internal Layout
//!
//! The layout of the inner allocation is exactly equivalent to `Rc<(usize, [T])>`, three `usize`
//! words plus the slice:
//!
//! ```text
//!  0        8       16       24..
//! |--------|--------|--------|-------~
//! | strong |  weak  | length | slice..
//! |--------|--------|--------|-------~
//! ```

use alloc::{
	alloc::Global,
	boxed::Box,
	string::String,
	vec::Vec as StdVec
};
use core::alloc::{AllocError, Allocator};
use core::cmp::Ordering;
use core::fmt;
use core::hash::{Hash, Hasher};
use core::mem::MaybeUninit;
use core::ops::{Deref, Index, RangeBounds};
use core::ptr::NonNull;
use core::slice::{ChunksExactMut, ChunksMut, Iter, IterMut, RChunksExactMut, RChunksMut, RSplitMut, RSplitNMut, SliceIndex, SplitInclusiveMut, SplitMut, SplitNMut};
#[cfg(feature = "array-vec")]
use crate::array::vec::ArrayVec;
use crate::error::{Result, Shared};
use crate::marker::RcVector;
pub(crate) use __private::Vec;
use drain::Drain;
use into_iter::IntoIter;
use unique::Unique;
use weak::Weak;

#[cfg(target_has_atomic = "ptr")]
pub mod arc;
pub mod rc;

pub(crate) mod drain;
mod eq;
pub(crate) mod into_iter;
pub(crate) mod unique;
pub(crate) mod weak;

// Workaround for "struct is private" error
mod __private {
	use alloc::alloc::Global;
	use core::alloc::Allocator;
	use core::marker::PhantomData;
	use crate::raw::RawVec;

	pub struct Vec<T, const ATOMIC: bool = false, A: Allocator = Global> {
		pub(crate) inner: RawVec<[T], A>,
		pub(crate) len: usize,
	}
}

impl<T, const ATOMIC: bool> Vec<T, ATOMIC> {
	/// Creates a new, empty vector.
	///
	/// No memory is allocated until elements are pushed to the vector. Until memory is allocated,
	/// the vector and any of its clones act as if they hold a [unique](Self::is_unique) reference,
	/// despite lacking an allocation to reference. Thus, they are all mutable.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::new();
	/// ```
	#[must_use]
	pub fn new() -> Self {
		Self::new_in(Global)
	}

	/// Constructs a new, empty vector with at least the specified capacity.
	/// 
	/// The vector will be able to hold at least `capacity` elements without reallocating. This
	/// method is allowed to allocate for more elements than the specified capacity. If the capacity
	/// is zero, the vector will not allocate.
	/// 
	/// If the vector element type is zero-sized, this will not allocate memory for any elements,
	/// and the capacity will always be [`usize::MAX`]. Memory will only be allocated for the
	/// reference counts.
	/// 
	/// # Panics
	/// 
	/// Panics if the capacity is greater than [`isize::MAX`] *bytes* minus three [`usize`] words.
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

impl<T, A: Allocator, const ATOMIC: bool> Vec<T, ATOMIC, A> {
	/// Creates a new, empty vector in the given allocator.
	///
	/// No memory is allocated until elements are pushed to the vector. Until memory is allocated,
	/// the vector and any of its clones act as if they hold a [unique](Self::is_unique) reference,
	/// despite lacking an allocation to reference. Thus, they are all mutable.
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
	/// let mut vec: Vec<i32, _> = Vec::new_in(System);
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
	/// is zero, the vector will not allocate.
	///
	/// If the vector element type is zero-sized, this will not allocate memory for any elements,
	/// and the capacity will always be [`usize::MAX`]. Memory will only be allocated for the
	/// reference counts.
	///
	/// # Panics
	///
	/// Panics if the capacity is greater than [`isize::MAX`] *bytes* minus three [`usize`] words.
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

	/// Returns the total number of elements the vector can hold without reallocating.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::with_capacity(10);
	/// vec.push(42);
	/// assert!(vec.capacity() >= 10);
	/// ```
	pub const fn capacity(&self) -> usize {
		todo!()
	}

	/// Returns a slice over the vector contents.
	///
	/// Equivalent to `&s[..]`.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::new();
	/// vec.extend([1, 2, 3]);
	///
	/// assert_eq!(vec.as_slice(), [1, 2, 3]);
	/// ```
	pub fn as_slice(&self) -> &[T] {
		todo!()
	}

	/// Returns a mutable slice over the vector contents, if the vector holds a unique reference.
	///
	/// # Errors
	///
	/// Returns an error if the vector holds a shared reference to its buffer.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([1, 2, 3, 4, 5, 6, 7, 8]);
	/// vec.try_as_mut_slice().unwrap().rotate_left(3);
	///
	/// assert_eq!(vec.as_slice(), [4, 5, 6, 7, 8, 1, 2, 3]);
	/// ```
	pub fn try_as_mut_slice(&mut self) -> Result<&mut [T]> {
		todo!()
	}

	/// Returns a raw pointer to the vector's buffer, or a dangling raw pointer valid for zero-sized
	/// reads if the vector didn't allocate.
	///
	/// The caller must ensure that the vector outlives the pointer this function returns, or else
	/// it will end up dangling. Modifying the vector may cause its buffer to be reallocated, which
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
	/// use sharevec::vec::rc::Vec;
	///
	/// let vec: Vec<i32> = Vec::from([1, 2, 4]);
	/// let ptr = vec.as_ptr();
	///
	/// unsafe {
	///     for i in 0..vec.len() {
	///         assert_eq!(*ptr.add(i), 1 << i);
	///     }
	/// }
	/// ```
	///
	/// Due to the aliasing guarantee, this code is valid:
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([1, 2, 3]);
	/// unsafe {
	///     let ptr1 = vec.as_ptr();
	///     assert_eq!(ptr1.read(), 1);
	///     let ptr2 = vec.as_mut_ptr().offset(2);
	///     ptr2.write(2);
	///     // Notably, writing to `ptr2` did *not* invalidate `ptr1`
	///     // because it mutated a different element:
	///     _ = ptr1.read();
	/// }
	/// ```
	pub fn as_ptr(&self) -> *const T {
		todo!()
	}
	/// Returns a raw pointer to the vector's buffer, or a dangling raw pointer valid for zero-sized
	/// reads if the vector didn't allocate.
	///
	/// The caller must ensure that the vector outlives the pointer this function returns, or else
	/// it will end up dangling. Modifying the vector may cause its buffer to be reallocated, which
	/// would also make any pointers to it invalid.
	///
	/// The caller must ensure that, for a [shared] buffer reference, the memory the pointer
	/// (non-transitively) points to is never written to (except inside an `UnsafeCell`) using this
	/// pointer or any pointer derived from it. The pointer must only be written to if the vector
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
	/// use sharevec::vec::rc::Vec;
	///
	/// let size = 8;
	/// let mut vec: Vec<i32> = Vec::with_capacity(size);
	/// let ptr = vec.as_mut_ptr();
	///
	/// // Initialize elements via raw pointer writes, then set length.
	/// // This is safe because no other strong reference points to the vector contents.
	/// unsafe {
	///     for i in 0..size {
	///         ptr.add(i).write(i as i32);
	///     }
	///     vec.set_len(size);
	/// }
	/// assert_eq!(vec, [1, 2, 3, 4, 5, 6, 7, 8]);
	/// ```
	///
	/// Due to the aliasing guarantee, this code is valid:
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([0]);
	/// unsafe {
	///     let ptr1 = vec.as_mut_ptr();
	///     ptr1.write(1);
	///     let ptr2 = vec.as_mut_ptr();
	///     ptr2.write(2);
	///     // Notably, writing to `ptr2` did *not* invalidate `ptr1`:
	///     ptr1.write(3);
	/// }
	/// ```
	pub fn as_mut_ptr(&mut self) -> *mut T {
		todo!()
	}
	/// Returns a `NonNull` pointer to the vector's buffer, or a dangling [`NonNull`] pointer valid
	/// for zero-sized reads if the vector didn't allocate.
	///
	/// The caller must ensure that the vector outlives the pointer this function returns, or else
	/// will end up dangling. Modifying the vector may cause its buffer to be reallocated, which
	/// would also make any pointers to it invalid.
	///
	/// The caller must ensure that, for a [shared] buffer reference, the memory the pointer
	/// (non-transitively) points to is never written to (except inside an `UnsafeCell`) using this
	/// pointer or any pointer derived from it. The pointer must only be written to if the vector
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
	/// use sharevec::vec::rc::Vec;
	///
	/// let size = 8;
	/// let mut vec: Vec<i32> = Vec::with_capacity(size);
	/// let ptr = vec.as_non_null();
	///
	/// // Initialize elements via raw pointer writes, then set length.
	/// // This is safe because no other strong reference points to the vector contents.
	/// unsafe {
	///     for i in 0..size {
	///         ptr.add(i).write(i as i32);
	///     }
	///     vec.set_len(size);
	/// }
	/// assert_eq!(vec, [1, 2, 3, 4, 5, 6, 7, 8]);
	/// ```
	///
	/// Due to the aliasing guarantee, this code is valid:
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([0]);
	/// unsafe {
	///     let ptr1 = vec.as_non_null();
	///     ptr1.write(1);
	///     let ptr2 = vec.as_non_null();
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

	/// Returns `true` if this vector holds the only strong reference to its allocated capacity,
	/// meaning no other vector shares it, allowing modification.
	///
	/// For empty vectors created with [`new`]/[`new_in`] which have not been modified, this returns
	/// `true`.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let vec: Vec<i32> = Vec::with_capacity(10);
	/// let weak = vec.demote();
	/// assert!(vec.is_unique());
	/// ```
	/// 
	/// Non-allocated vectors are always unique, even when cloned:
	/// 
	/// ```
	/// use sharevec::vec::rc::Vec;
	/// 
	/// let vec: Vec<i32> = Vec::new();
	/// let vec2 = vec.clone();
	/// assert!(vec.is_unique());
	/// assert!(vec2.is_unique());
	/// ```
	pub fn is_unique(&self) -> bool {
		self.strong_count() <= 1
	}
	/// Returns `true` if this vector does not hold the only reference to its allocated capacity,
	/// making it read-only. Only strong references count toward sharing.
	///
	/// For empty vectors created with [`new`]/[`new_in`] which have not been modified, this returns
	/// `false`.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let vec: Vec<i32> = Vec::with_capacity(10);
	/// let clone = vec.clone();
	/// assert!(vec.is_shared());
	/// ```
	///
	/// Non-allocated vectors are never shared, even when cloned:
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let vec: Vec<i32> = Vec::new();
	/// let vec2 = vec.clone();
	/// assert!(!vec.is_shared());
	/// assert!(!vec2.is_shared());
	/// ```
	pub fn is_shared(&self) -> bool {
		!self.is_unique()
	}
	/// Returns `true` if this vector's allocated capacity is *not* weakly referenced.
	///
	/// For empty vectors created with [`new`]/[`new_in`] which have not been modified, this returns
	/// `true`.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let vec: Vec<i32> = Vec::with_capacity(10);
	/// assert!(vec.is_weakly_unique());
	/// ```
	/// 
	/// Non-allocated vectors are never weakly referenced:
	/// 
	/// ```
	/// use sharevec::vec::rc::Vec;
	/// 
	/// let vec: Vec<i32> = Vec::new();
	/// let weak = vec.demote(); // Dangling
	/// assert!(vec.is_weakly_unique());
	/// ```
	pub fn is_weakly_unique(&self) -> bool {
		self.weak_count() == 0
	}
	/// Returns `true` if this vector's allocated capacity is weakly referenced.
	///
	/// For empty vectors created with [`new`]/[`new_in`] which have not been modified, this returns
	/// `false`.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let vec: Vec<i32> = Vec::with_capacity(10);
	/// let weak = vec.demote();
	/// assert!(vec.is_weakly_shared());
	/// ```
	///
	/// Non-allocated vectors are never weakly referenced:
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let vec: Vec<i32> = Vec::new();
	/// let weak = vec.demote(); // Dangling
	/// assert!(!vec.is_weakly_shared());
	/// ```
	pub fn is_weakly_shared(&self) -> bool {
		!self.is_weakly_unique()
	}

	/// Returns the number of strong references to the vector's allocated capacity.
	/// 
	/// For empty vectors created with [`new`]/[`new_in`] which have not been modified, this returns
	/// `0`.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let vec: Vec<i32> = Vec::with_capacity(10);
	/// let clone = vec.clone();
	/// assert_eq!(vec.strong_count(), 2);
	/// ```
	/// 
	/// Non-allocated vectors hold no strong references:
	/// 
	/// ```
	/// use sharevec::vec::rc::Vec;
	/// 
	/// let vec: Vec<i32> = Vec::new();
	/// assert_eq!(vec.strong_count(), 0);
	/// let vec2 = vec.clone();
	/// assert_eq!(vec.strong_count(), 0);
	/// assert_eq!(vec2.strong_count(), 0);
	/// ```
	pub fn strong_count(&self) -> usize {
		todo!()
	}
	/// Returns the number of weak references to the vector's allocated capacity.
	///
	/// For empty vectors created with [`new`]/[`new_in`] which have not been modified, this returns
	/// `0`.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let vec: Vec<i32> = Vec::with_capacity(10);
	/// let weak = vec.demote();
	/// assert_eq!(vec.weak_count(), 1);
	/// ```
	///
	/// Non-allocated vectors are never weakly referenced:
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let vec: Vec<i32> = Vec::new();
	/// let weak = vec.demote(); // Dangling
	/// assert_eq!(vec.weak_count(), 0);
	/// ```
	pub fn weak_count(&self) -> usize {
		todo!()
	}

	/// If the vector is unique, returns a mutable view of the unique allocation.
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
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::new();
	///
	/// let mut unique = vec.unique().unwrap();
	/// unique.push(1);
	/// unique.push(2);
	/// unique.push(3);
	/// drop(unique);
	///
	/// let clone = vec.clone();
	/// assert!(vec.unique().is_err());
	/// drop(clone);
	///
	/// let weak = vec.demote();
	/// assert!(vec.unique().is_err());
	/// ```
	pub fn unique(&mut self) -> Result<Unique<T, A, ATOMIC>> {
		todo!()
	}
	
	/// Reserves space for at least `additional` elements. The vector may reserve more space to
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
	/// Panics if the new capacity is greater than [`isize::MAX`] *bytes* minus three [`usize`]
	/// words.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	/// 
	/// let mut vec: Vec<i32> = Vec::from([1]);
	/// assert_eq!(vec.try_reserve(10), Ok(()));
	/// assert!(vec.capacity() >= 11);
	/// ```
	pub fn try_reserve(&mut self, additional: usize) -> Result {
		todo!()
	}

	/// Reserves the minimum space for at least `additional` elements, without speculative
	/// over-allocation [`try_reserve`] and [`reserve`] do. The reserved will be greater than or
	/// equal to `length + additional`. No memory is allocated if the capacity is already sufficient.
	///
	/// The allocator may give the vector more space than it requests. Therefore, capacity cannot be
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
	/// Panics if the new capacity is greater than [`isize::MAX`] *bytes* minus three [`usize`]
	/// words.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([1]);
	/// assert_eq!(vec.try_reserve_exact(10), Ok(()));
	/// assert!(vec.capacity() >= 11);
	/// ```
	pub fn try_reserve_exact(&mut self, additional: usize) -> Result {
		todo!()
	}
	
	// Todo: try_reserve with errors instead of panics, similar to Vec::try_reserve?

	/// Shrinks the capacity of the vector as much as possible.
	///
	/// The behavior of this method depends on the allocator, which may either shrink the vector
	/// in-place or reallocate. The resulting vector might still have some excess capacity, just as
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
	/// use sharevec::vec::rc::Vec;
	/// 
	/// let mut vec: Vec<i32> = Vec::with_capacity(10);
	/// vec.extend([1, 2, 3]);
	/// assert!(vec.capacity() >= 10);
	/// assert_eq!(vec.try_shrink_to_fit(), Ok(()));
	/// assert!(vec.capacity() >= 3);
	/// ```
	pub fn try_shrink_to_fit(&mut self) -> Result {
		todo!()
	}

	/// Shrinks the capacity of the vector with a lower bound.
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
	/// use sharevec::vec::rc::Vec;
	/// 
	/// let mut vec: Vec<i32> = Vec::with_capacity(10);
	/// vec.extend([1, 2, 3]);
	/// assert!(vec.capacity() >= 10);
	/// assert_eq!(vec.try_shrink_to(4), Ok(()));
	/// assert!(vec.capacity() >= 4);
	/// assert_eq!(vec.try_shrink_to(0), Ok(()));
	/// assert!(vec.capacity() >= 3);
	/// ```
	pub fn try_shrink_to(&mut self, min_capacity: usize) -> Result {
		todo!()
	}

	/// Shortens the vector, keeping the first `len` elements and dropping the rest. If `len` is
	/// greater or equal to the vector's current length, this has no effect.
	///
	/// # Leaking
	///
	/// Because memory may be shared and each shared vector may have a different length, truncation
	/// may cause elements outside `len` to go out of scope without dropping. The elements' [`Drop`]
	/// implementation can only be safely called when the vector holds a unique reference.
	///
	/// Rust does not require [`Drop::drop`] to be called, but this may be undesirable behavior for
	/// types with a non-trivial `drop` implementation. For such types, use [`unique`]/[`as_unique`]
	/// to get a mutable view which is guaranteed to drop elements, or [`is_unique`] to check for a
	/// unique reference.
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
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
	/// let mut vec1 = Vec::from([
	///     WithDrop { val: 0 },
	///     WithDrop { val: 1 },
	///     WithDrop { val: 2 }
	/// ]);
	/// let mut vec2 = vec1.clone();
	///
	/// vec1.truncate(2);
	/// vec2.truncate(1);
	/// // The last element hasn't been dropped as would be expected, but it's become inaccessible
	/// assert_eq!(vec1.len(), 2);
	/// assert_eq!(vec2.len(), 1);
	///
	/// // Now only the first element is accessible. None of them have been dropped.
	/// drop(vec1);
	/// assert_eq!(vec2[0].val, 0);
	/// assert!(vec2.get(1).is_none());
	///
	/// // The second and third elements could be overwritten without dropping!
	/// vec2.try_push(WithDrop { val: 3 }).unwrap();
	/// vec2.try_push(WithDrop { val: 4 }).unwrap();
	/// // Output:
	/// // Dropping 3
	/// // Dropping 4
	/// vec2.truncate(1);
	///
	/// vec2.try_push(WithDrop { val: 1 }).unwrap();
	/// vec2.try_push(WithDrop { val: 2 }).unwrap();
	/// let mut vec = vec2.clone();
	/// // We've leaked the elements again
	/// vec.truncate(1);
	/// drop(vec2);
	///
	/// // We know the elements are still in memory, and `vec` now uniquely references them. So, an
	/// // unsafe workaround can recover the lost elements so they can be dropped.
	/// unsafe {
	///     vec.set_len(3);
	///     // Output:
	///     // Dropping 1
	///     // Dropping 2
	///     vec.truncate(1);
	/// }
	/// ```
	///
	/// [`unique`]: Self::unique
	/// [`as_unique`]: Self::as_unique
	/// [`is_unique`]: Self::is_unique
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([1, 2, 3, 4, 5]);
	/// // Truncates from 5 elements to 2
	/// vec.truncate(2);
	/// assert_eq!(vec, [1, 2]);
	/// // No truncation occurs when the length is greater than the vector's current length
	/// vec.truncate(8);
	/// assert_eq!(vec, [1, 2]);
	/// // Truncating to 0 elements is equivalent to `clear`
	/// vec.truncate(0);
	/// assert_eq!(vec, []);
	/// ```
	pub fn truncate(&mut self, len: usize) {
		todo!()
	}

	/// Clears the vector, removing all values.
	///
	/// # Leaking
	///
	/// Because memory may be shared and each shared vector may have a different length, clearing
	/// may cause all elements to go out of scope without dropping. The elements' [`Drop`]
	/// implementation can only be safely called when the vector holds a unique reference.
	///
	/// Rust does not require [`Drop::drop`] to be called, but this may be undesirable behavior for
	/// types with a non-trivial `drop` implementation. For such types, use [`unique`]/[`as_unique`]
	/// to get a mutable view which is guaranteed to drop elements, or [`is_unique`] to check for a
	/// unique reference.
	///
	/// ```
	/// use sharevec::vec::arc::Vec;
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
	/// let mut vec1 = Vec::from([
	///     WithDrop { val: 0 },
	///     WithDrop { val: 1 },
	///     WithDrop { val: 2 }
	/// ]);
	/// let mut vec2 = vec1.clone();
	///
	/// vec1.clear();
	/// vec2.clear();
	/// // The elements haven't been dropped as would be expected, but they've become inaccessible
	/// assert!(vec1.is_empty());
	/// assert!(vec2.is_empty());
	/// drop(vec2);
	///
	/// // Any of the elements could be overwritten without dropping!
	/// vec1.try_push(WithDrop { val: 3 }).unwrap();
	/// // Output:
	/// // Dropping 3
	/// vec1.clear();
	///
	/// vec1.try_push(WithDrop { val: 0 }).unwrap();
	///
	/// // We know the elements are still in memory, and `vec1` now uniquely references them. So, an
	/// // unsafe workaround can recover the lost elements so they can be dropped.
	/// unsafe {
	///     vec1.set_len(3);
	///     // Output:
	///     // Dropping 0
	///     // Dropping 1
	///     // Dropping 2
	///     vec1.clear();
	/// }
	/// ```
	///
	/// [`unique`]: Self::unique
	/// [`as_unique`]: Self::as_unique
	/// [`is_unique`]: Self::is_unique
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([1, 2, 3]);
	/// vec.clear();
	///
	/// assert_eq!(vec, []);
	/// ```
	pub fn clear(&mut self) {
		todo!()
	}

	/// Forces the vector length to `new_len`, assuming elements outside the current length have
	/// initialized.
	///
	/// This exposes internal behavior, meant to be used after elements have been initialized with
	/// [`spare_capacity_mut`]. Usually changing the length of the vector should be done with safe
	/// operations: [`truncate`], [`resize`], [`extend`], [`clear`], etc.
	///
	/// [`spare_capacity_mut`]: Self::spare_capacity_mut
	/// [`truncate`]: Self::truncate
	/// [`resize`]: Self::resize
	/// [`extend`]: Extend::extend
	/// [`clear`]: Self::clear
	///
	/// # Safety
	///
	/// `new_len` must be less than or equal to the capacity. The elements from the old length to
	/// `new_len` must be initialized. This implies that the vector contains a unique reference, as
	/// no elements outside the old length could've been initialized with a shared reference.
	///
	/// # Examples
	///
	/// See [`spare_capacity_mut`] for an example with safe initialization of capacity elements and
	/// use of this method.
	///
	/// [`spare_capacity_mut`]: Self::spare_capacity_mut
	pub unsafe fn set_len(&mut self, new_len: usize) {
		todo!()
	}

	/// Removes and returns the element at position `index` from the vector, replacing this element
	/// with the last element in the vector. This doesn't preserve ordering of the remaining
	/// elements, but is *O*(1). If ordering must be preserved, use [`try_remove`].
	///
	/// [`try_remove`]: Self::try_remove
	///
	/// # Errors
	///
	/// Returns an error if the vector is immutable because it holds a shared reference to its
	/// buffer.
	///
	/// # Panics
	///
	/// Panics if `index` is greater than the vector length.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec = Vec::from(['a', 'b', 'c', 'd']);
	///
	/// assert_eq!(vec.try_swap_remove(1), Ok('b'));
	/// assert_eq!(vec, ['a', 'd', 'c']);
	///
	/// assert_eq!(vec.try_swap_remove(0), Ok('a'));
	/// assert_eq!(vec, ['c', 'd']);
	/// ```
	///
	/// # Time complexity
	///
	/// Takes *O*(1) time.
	pub fn try_swap_remove(&mut self, index: usize) -> Result<T> {
		todo!()
	}

	/// Removes and returns the element at position `index` from the vector, shifting all subsequent
	/// elements to the left.
	///
	/// # Errors
	///
	/// Returns an error if the vector is immutable because it holds a shared reference to its
	/// buffer.
	///
	/// # Panics
	///
	/// Panics if `index` is greater than the vector length.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec = Vec::from(['a', 'b', 'c']);
	/// assert_eq!(vec.try_remove(1), Ok('b'));
	/// assert_eq!(vec, ['a', 'c']);
	/// ```
	///
	/// # Time complexity
	///
	/// Takes at most *O*(*n*) time, as all elements after `index` must be shifted. In the worst
	/// case, all [`len`] elements must be shifted when `index` is `0`. If element ordering is not
	/// important, use [`try_swap_remove`] instead, which is *O*(1). If you need to remove elements
	/// from the beginning of the vector frequently and need to preserve ordering, consider
	/// [`Deque::try_pop_front`], which is also *O*(1).
	///
	/// [`len`]: Self::len
	/// [`try_swap_remove`]: Self::try_swap_remove
	/// [`Deque::try_pop_front`]: crate::deque::Deque::try_pop_front
	pub fn try_remove(&mut self, index: usize) -> Result<T> {
		todo!()
	}

	/// Inserts an element at position `index` within the vector, shifting all subsequent elements to
	/// the right.
	///
	/// # Errors
	///
	/// Returns an error if the vector is immutable because it holds a shared reference to its
	/// buffer.
	///
	/// # Panics
	///
	/// Panics if `index` is greater than the vector length.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<char> = Vec::from(['a', 'c']);
	/// assert_eq!(vec.try_insert(1, 'b'), Ok(()));
	/// assert_eq!(vec, ['a', 'b', 'c']);
	/// assert_eq!(vec.try_insert(3, 'd'), Ok(()));
	/// assert_eq!(vec, ['a', 'b', 'c', 'd']);
	/// ```
	///
	/// # Time complexity
	///
	/// Takes at most *O*(*n*) time, as all elements after `index` must be shifted. In the worst
	/// case, all [`len`] elements must be shifted when `index` is `0`.
	///
	/// [`len`]: Self::len
	pub fn try_insert(&mut self, index: usize, element: T) -> Result {
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
	/// Returns an error if the vector is immutable because it holds a shared reference to its
	/// buffer.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([1, 2, 3, 4]);
	/// assert_eq!(vec.try_retain(|&x| x % 2 == 0), Ok(()));
	/// assert_eq!(vec, [2, 4]);
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
	/// Returns an error if the vector is immutable because it holds a shared reference to its
	/// buffer.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([1, 2, 3, 4]);
	/// assert_eq!(
	///     vec.try_retain_mut(|x| if *x % 2 == 0 {
	///         *x += 1;
	///         true
	///     } else {
	///         false
	///     }),
	///     Ok(())
	/// );
	/// assert_eq!(vec, [3, 5]);
	/// ```
	pub fn try_retain_mut<F: FnMut(&mut T) -> bool>(&mut self, predicate: F) -> Result {
		todo!()
	}

	/// Removes consecutive repeated elements from the vector according to the [`PartialEq`] trait
	/// implementation. If the vector is sorted, all duplicates are removed.
	///
	/// # Errors
	///
	/// Returns an error if the vector is immutable because it holds a shared reference to its
	/// buffer.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([1, 2, 2, 3, 2]);
	/// assert_eq!(vec.try_dedup(), Ok(()));
	/// assert_eq!(vec, [1, 2, 3, 2]);
	/// ```
	pub fn try_dedup(&mut self) -> Result
	where T: PartialEq {
		self.try_dedup_by(|a, b| a == b)
	}
	/// Removes consecutive repeated elements from the vector that resolve to the same key given by
	/// `key`. If the vector is sorted, all duplicates are removed.
	///
	/// # Errors
	///
	/// Returns an error if the vector is immutable because it holds a shared reference to its
	/// buffer.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([10, 20, 21, 30, 20]);
	/// assert_eq!(vec.try_dedup_by_key(|&mut x| x / 10), Ok(()));
	/// assert_eq!(vec, [10, 20, 30, 20]);
	/// ```
	pub fn try_dedup_by_key<F: FnMut(&mut T) -> K, K: PartialEq>(&mut self, mut key: F) -> Result {
		self.try_dedup_by(|a, b| key(a) == key(b))
	}
	/// Removes consecutive repeated elements from the vector that satisfy an equality `predicate`.
	/// If the vector is sorted, all duplicates are removed.
	///
	/// The `predicate` function is passed references to two elements from the vector and determines
	/// if the elements are equal. The elements are passed in opposite order, such that if
	/// `predicate(a, b)` returns `true`, element `a` is removed.
	///
	/// # Errors
	///
	/// Returns an error if the vector is immutable because it holds a shared reference to its
	/// buffer.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<char> = Vec::from(['a', 'A', 'b', 'c', 'c', 'B']);
	/// assert_eq!(vec.try_dedup_by(|a, b| a.eq_ignore_ascii_case(b)), Ok(()));
	/// assert_eq!(vec, ['a', 'b', 'c', 'B']);
	/// ```
	pub fn try_dedup_by<F: FnMut(&mut T, &mut T) -> bool>(&mut self, predicate: F) -> Result {
		todo!()
	}

	/// Appends an element to the end of the vector if there is sufficient spare capacity, otherwise
	/// returns an error containing the element.
	///
	/// # Errors
	///
	/// Returns an error if the vector is immutable because it holds a shared reference to its
	/// buffer.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::new();
	/// assert_eq!(vec.try_push(1), Ok(()));
	/// assert_eq!(vec.try_push(2), Ok(()));
	/// ```
	///
	/// # Time complexity
	///
	/// Takes *O*(1) time.
	pub fn try_push(&mut self, value: T) -> Result {
		todo!()
	}

	/// Removes and returns the last element from the vector, or [`None`] if it is empty.
	///
	/// # Errors
	///
	/// Returns an error if the vector is immutable because it holds a shared reference to its
	/// buffer.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([1, 2]);
	/// assert_eq!(vec.try_pop(), Ok(Some(2)));
	/// assert_eq!(vec.try_pop(), Ok(Some(1)));
	/// assert_eq!(vec.try_pop(), Ok(None));
	/// ```
	///
	/// # Time complexity
	///
	/// Takes *O*(1) time.
	pub fn try_pop(&mut self) -> Result<Option<T>> {
		todo!()
	}

	/// Removes and returns the last element from the vector if the predicate returns `true`, or
	/// `None` if predicate returns `false` or the vector is empty. If the vector is empty, the
	/// predicate is not called.
	///
	/// # Errors
	///
	/// Returns an error if the vector is immutable because it holds a shared reference to its
	/// buffer. The predicate is not called in this case.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([1, 2, 3, 4]);
	/// let even = |x: &mut i32| *x % 2 == 0;
	/// assert_eq!(vec.try_pop_if(even), Ok(Some(4)));
	/// assert_eq!(vec, [1, 2, 3]);
	/// assert_eq!(vec.try_pop_if(even), Ok(None));
	/// ```
	///
	/// # Time complexity
	///
	/// Takes *O*(1) time.
	pub fn try_pop_if<F: FnOnce(&mut T) -> bool>(&mut self, predicate: F) -> Result<Option<T>> {
		todo!()
	}

	/// Moves all elements from `other` into this vector, leaving `other` empty. Any like[^atomic]
	/// vector type from this crate may be appended, even array vectors with a different fixed
	/// capacity.
	///
	/// [^atomic]: the only restriction is that both vectors must either be atomic or non-atomic;
	/// atomic vectors may be only appended to other atomic vectors, non-atomic vectors may only be
	/// appended to other non-atomic vectors.
	///
	/// # Errors
	///
	/// Returns an error if either of the vectors are immutable because they hold a shared reference
	/// to their respective buffers. In this case, neither vector is modified.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec1: Vec<i32> = Vec::from([1, 2, 3]);
	/// let mut vec2 = Vec::from([4, 5, 6]);
	/// assert_eq!(vec1.try_append(&mut vec2), Ok(()));
	/// assert_eq!(vec1, [1, 2, 3, 4, 5, 6]);
	/// assert_eq!(vec2, []);
	/// ```
	pub fn try_append<V: RcVector<T, A, ATOMIC> + ?Sized>(&mut self, other: &mut V) -> Result {
		todo!()
	}

	/// Removes the specified range from the vector, returning all removed elements as an iterator.
	/// If the iterator is dropped before being fully consumed, the remaining removed elements are
	/// dropped.
	///
	/// # Panics
	///
	/// Panics if the starting point is greater than the end point or if the end point is greater
	/// than the length of the vector.
	///
	/// # Errors
	///
	/// Returns an error if the vector is immutable because it holds a shared reference to its
	/// buffer.
	///
	/// # Leaking
	///
	/// If the returned iterator goes out of scope without being dropped (due to [`forget`], for
	/// example), the vector may have lost and leaked elements arbitrarily, including elements
	/// outside the range.
	///
	/// [`forget`]: core::mem::forget
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([1, 2, 3, 4, 5, 6, 7, 8]);
	/// let removed = vec.try_drain(2..6).map(Iterator::collect::<Vec<_>>);
	/// assert_eq!(removed, Ok([3, 4, 5, 6].into()));
	/// assert_eq!(vec, [1, 2, 7, 8]);
	/// ```
	pub fn try_drain<R: RangeBounds<usize>>(&mut self, range: R) -> Result<Drain<T, A, ATOMIC>> {
		todo!()
	}

	/// Returns the number of elements in the vector.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let vec = Vec::from([1, 2, 3]);
	/// assert_eq!(vec.len(), 3);
	/// ```
	pub fn len(&self) -> usize {
		todo!()
	}
	/// Returns `true` if the vector contains no elements.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::new();
	/// assert!(vec.is_empty());
	///
	/// vec.push(1);
	/// assert!(!vec.is_empty());
	/// ```
	pub fn is_empty(&self) -> bool {
		self.len() == 0
	}
	/// Returns `true` if the vector contains any elements.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::new();
	/// assert!(!vec.is_not_empty());
	///
	/// vec.push(1);
	/// assert!(vec.is_not_empty());
	/// ```
	pub fn is_not_empty(&self) -> bool {
		!self.is_empty()
	}
	/// Returns `true` if the vector cannot hold any more elements without resizing.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec = Vec::from([1, 2, 3]);
	/// assert!(vec.is_full());
	///
	/// vec.pop();
	/// assert!(!vec.is_full());
	/// ```
	pub fn is_full(&self) -> bool {
		self.len() == self.capacity()
	}
	/// Returns `true` if the vector can hold more elements without resizing.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec = Vec::from([1, 2, 3]);
	/// assert!(!vec.is_not_full());
	///
	/// vec.pop();
	/// assert!(vec.is_not_full());
	/// ```
	pub fn is_not_full(&self) -> bool {
		!self.is_full()
	}

	/// Splits the vector into two at the given index.
	///
	/// Returns a new vector containing the elements starting from the given index. The original is
	/// left containing the elements up to `at` (exclusive).
	///
	/// - If you want to take ownership of the entire contents and capacity of the vector, use
	///   [`mem::take`] or [`mem::replace`].
	/// - If you don't need the returned vector at all, see [`truncate`].
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
	/// Panics if `at` is greater than the vector length.
	///
	/// # Errors
	///
	/// Returns an error if the vector is immutable because it holds a shared reference to its
	/// buffer.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec = Vec::from([1, 2, 3, 4]);
	/// assert_eq!(vec.try_split_off(2), Ok([3, 4].into()));
	/// assert_eq!(vec, [1, 2]);
	/// ```
	pub fn try_split_off(&mut self, at: usize) -> Result<Self> where A: Clone {
		todo!()
	}

	/// Resizes the vector in-place to the specified length.
	///
	/// If `new_len` is greater than the current length, the vector is extended, filling the
	/// additional space with element returned from calling the closure `fill`. If `new_len` is less
	/// than the current length, the vector is truncated.
	///
	/// To fill the additional space by [`Clone`]ing a given value, use [`try_resize`]. To fill with
	/// default values, pass [`Default::default`] as the second argument.
	///
	/// [`try_resize`]: Self::try_resize
	///
	/// # Leaking
	///
	/// If the vector is truncated, the same leaking caveats as [`truncate`] apply.
	///
	/// [`truncate`]: Self::truncate#leaking
	///
	/// # Errors
	///
	/// Returns an error if the vector is immutable because it holds a shared reference to its
	/// buffer.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([1, 2, 3]);
	/// let fill = Default::default;
	///
	/// assert_eq!(vec.try_resize_with(5, fill), Ok(()));
	/// assert_eq!(vec, [1, 2, 3, 0, 0]);
	/// assert_eq!(vec.try_resize_with(3, fill), Ok(()));
	/// assert_eq!(vec, [1, 2, 3]);
	/// ```
	pub fn try_resize_with<F: FnMut() -> T>(&mut self, new_len: usize, fill: F) -> Result {
		todo!()
	}

	/// Returns the remaining spare capacity of the vector as a slice of uninitialized elements.
	///
	/// The returned slice can be used to fill the vector, before marking the data as initialized
	/// with [`set_len`].
	///
	/// [`set_len`]: Self::set_len
	///
	/// # Errors
	///
	/// Returns an error if the vector is immutable because it holds a shared reference to its
	/// buffer.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::with_capacity(3);
	///
	/// let spare = vec.try_spare_capacity_mut().unwrap();
	/// spare[0].write(0);
	/// spare[1].write(1);
	/// spare[2].write(2);
	///
	/// unsafe {
	///     vec.set_len(3);
	/// }
	///
	/// assert_eq!(vec, [0, 1, 2]);
	/// ```
	pub fn try_spare_capacity_mut(&mut self) -> Result<&mut [MaybeUninit<T>]> {
		todo!()
	}

	/// Mutably indexes the vector, if it holds a unique reference.
	///
	/// To use the `vector[index]` syntax, use [`unique`]/[`as_unique`] to get a [`Unique`] wrapper.
	///
	/// [`unique`]: Self::unique
	/// [`as_unique`]: Self::as_unique
	///
	/// # Errors
	///
	/// Returns an error if the vector is immutable because it holds a shared reference to its
	/// buffer.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([1, 2, 3]);
	///
	/// for i in 0..vec.len() {
	///     *vec.try_index_mut(i).unwrap() = i as i32 * 2;
	/// }
	/// assert_eq!(vec, [2, 4, 6]);
	///
	/// // `vec.try_index_mut(4)` would panic
	/// ```
	pub fn try_index_mut<I: SliceIndex<[T]>>(&mut self, index: I) -> Result<&mut <Self as Index<I>>::Output> {
		todo!()
	}

	/// Appends elements from an iterator to the vector.
	///
	/// # Errors
	///
	/// Returns an error if the vector is immutable because it holds a shared reference to its
	/// buffer.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::new();
	/// assert_eq!(vec.try_extend([1, 2]), Ok(()));
	/// assert_eq!(vec, [1, 2]);
	/// ```
	pub fn try_extend<I: IntoIterator<Item = T>>(&mut self, iter: I) -> Result<(), Shared<I>> {
		todo!()
	}
	/// Appends referenced elements from an iterator to the vector by copying.
	///
	/// # Errors
	///
	///
	/// Returns an error if the vector is immutable because it holds a shared reference to its
	/// buffer.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::new();
	/// assert_eq!(vec.try_extend_ref(&[1, 2]), Ok(()));
	/// assert_eq!(vec, [1, 2]);
	/// ```
	pub fn try_extend_ref<'a, I: IntoIterator<Item = &'a T>>(&mut self, iter: I) -> Result<(), Shared<I>> where T: Copy + 'a {
		todo!()
	}

	/// Consumes the vector, returning an iterator over its contents.
	///
	/// # Errors
	///
	/// Returns an error if the vector holds a shared reference to its buffer.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([1, 2, 3]);
	/// let mut iter = vec.try_into_iter().unwrap();
	/// assert!(iter.eq([1, 2, 3]));
	/// ```
	pub fn try_into_iter(self) -> Result<IntoIter<T, A, ATOMIC>, Self> {
		todo!()
	}

	/// Attempts to convert the variable-capacity vector into a fixed-capacity vector of capacity
	/// `N`.
	///
	/// If the capacity is equal to `N`, the conversion may be done even when the vector is shared.
	/// It takes *O*(1) time, and does not allocate memory. Otherwise, the vector will be resized if
	/// it holds a unique reference. This may allocate memory.
	/// 
	/// # Errors
	/// 
	/// Returns the original vector back as an error if:
	/// - its length is greater than `N`
	/// - its capacity is not equal to `N` and it cannot be resized because it holds a shared
	///   reference to its buffer
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	/// use sharevec::array::TryInsert;
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let vec: Vec<i32> = Vec::from([1, 2, 3]);
	/// if let Ok(mut array_vec) = vec.into_array_vec::<3>() {
	///     // The vector now can't grow its capacity beyond the fixed capacity.
	///     assert_eq!(array_vec.try_push(4), Err(TryInsert::FullCapacity { element: 4 }));
	/// }
	/// ```
	#[cfg(feature = "array-vec")]
	pub fn into_array_vec<const N: usize>(mut self) -> Result<ArrayVec<T, N, ATOMIC, A>, Self> {
		if self.len() > N {
			Err(self)
		} else {
			let Ok(()) = self.try_shrink_to(N) else { return Err(self) };
			todo!("convert")
		}
	}
}

impl<T: Clone, A: Allocator, const ATOMIC: bool> Vec<T, ATOMIC, A> {
	/// Resizes the vector in-place to the specified length, cloning `value` into additional space
	/// as needed.
	///
	/// If `new_len` is greater than the current length, the vector is extended, filling the
	/// additional space with `value`. If `new_len` is less than the current length, the vector is
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
	/// Returns an error if the vector is immutable because it holds a shared reference to its
	/// buffer.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([1, 2, 3]);
	///
	/// assert_eq!(vec.try_resize(5, 0), Ok(()));
	/// assert_eq!(vec, [1, 2, 3, 0, 0]);
	/// assert_eq!(vec.try_resize(3, 0), Ok(()));
	/// assert_eq!(vec, [1, 2, 3]);
	/// ```
	pub fn try_resize(&mut self, new_len: usize, value: T) -> Result {
		todo!()
	}

	/// Clones and appends all elements in a slice to the vector.
	///
	/// # Errors
	///
	/// Returns an error if the vector is immutable because it holds a shared reference to its
	/// buffer.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::new();
	/// assert_eq!(vec.try_extend_from_slice(&[1, 2, 3]), Ok(()));
	/// assert_eq!(vec, [1, 2, 3]);
	/// ```
	pub fn try_extend_from_slice(&mut self, other: &[T]) -> Result {
		todo!()
	}
	/// Clones and appends elements from `range` to the end of the vector.
	///
	/// # Panics
	///
	/// Panics if the start of the range is greater than the end or if the end of the range is
	/// greater than the length of the vector.
	///
	/// # Errors
	///
	/// Returns an error if the vector is immutable because it holds a shared reference to its
	/// buffer.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([1, 2, 3, 4]);
	/// assert_eq!(vec.try_extend_from_within(1..3), Ok(()));
	/// assert_eq!(vec, [1, 2, 3, 4, 2, 3]);
	/// ```
	pub fn try_extend_from_within<R: RangeBounds<usize>>(&mut self, range: R) -> Result {
		todo!()
	}
}

// Mutable slice operations
impl<T, A: Allocator, const ATOMIC: bool> Vec<T, ATOMIC, A> {
	/// Returns a mutable reference to the first element of the vector, or `None` if it is empty.
	///
	/// # Errors
	///
	/// Returns an error if the vector is not empty and holds a shared reference to its buffer. If
	/// the vector is empty, `None` is always returned.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([0, 1, 2]);
	///
	/// if let Ok(Some(first)) = vec.try_first_mut() {
	///     *first = 5;
	/// }
	/// assert_eq!(vec, [5, 1, 2]);
	///
	/// vec.clear();
	/// assert_eq!(vec.try_first_mut(), Ok(None));
	/// ```
	pub fn try_first_mut(&mut self) -> Result<Option<&mut T>> {
		self.try_as_mut_slice().map(<[_]>::first_mut)
	}

	/// Returns a mutable reference to the last element of the vector, or `None` if it is empty.
	///
	/// # Errors
	///
	/// Returns an error if the vector is not empty and holds a shared reference to its buffer. If
	/// the vector is empty, `None` is always returned.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([0, 1, 2]);
	///
	/// if let Ok(Some(last)) = vec.try_last_mut() {
	///     *last = 5;
	/// }
	/// assert_eq!(vec, [0, 1, 5]);
	///
	/// vec.clear();
	/// assert_eq!(vec.try_last_mut(), Ok(None));
	/// ```
	pub fn try_last_mut(&mut self) -> Result<Option<&mut T>> {
		self.try_as_mut_slice().map(<[_]>::last_mut)
	}

	/// Returns a mutable reference to the first element and the remaining slice of the vector, or
	/// `None` if it is empty.
	///
	/// # Errors
	///
	/// Returns an error if the vector is not empty and holds a shared reference to its buffer. If
	/// the vector is empty, `None` is always returned.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([0, 1, 2]);
	///
	/// if let Ok(Some((first, rest))) = vec.try_split_first_mut() {
	///     *first = 3;
	///     rest[0] = 4;
	///     rest[1] = 5;
	/// }
	/// assert_eq!(vec, [3, 4, 5]);
	///
	/// vec.clear();
	/// assert_eq!(vec.try_split_first_mut(), Ok(None));
	/// ```
	pub fn try_split_first_mut(&mut self) -> Result<Option<(&mut T, &mut [T])>> {
		self.try_as_mut_slice().map(<[_]>::split_first_mut)
	}

	/// Returns a mutable reference to the last element and the remaining slice of the vector, or
	/// `None` if it is empty.
	///
	/// # Errors
	///
	/// Returns an error if the vector is not empty and holds a shared reference to its buffer. If
	/// the vector is empty, `None` is always returned.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([0, 1, 2]);
	///
	/// if let Ok(Some((last, rest))) = vec.try_split_last_mut() {
	///     *last = 3;
	///     rest[0] = 4;
	///     rest[1] = 5;
	/// }
	/// assert_eq!(vec, [4, 5, 3]);
	///
	/// vec.clear();
	/// assert_eq!(vec.try_split_last_mut(), Ok(None));
	/// ```
	pub fn try_split_last_mut(&mut self) -> Result<Option<(&mut T, &mut [T])>> {
		self.try_as_mut_slice().map(<[_]>::split_last_mut)
	}

	/// Returns a mutable reference to the first `SIZE` elements of the vector, or `None` if the
	/// vector contains less than `SIZE` elements.
	///
	/// # Errors
	///
	/// Returns an error if the vector contains at least `SIZE` elements but holds a shared
	/// reference to its buffer. If the vector contains less than `SIZE` elements, `None` is always
	/// returned.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([0, 1, 2]);
	///
	/// if let Ok(Some(first)) = vec.try_first_chunk_mut::<2>() {
	///     *first = [5, 4];
	/// }
	/// assert_eq!(vec, [5, 4, 2]);
	///
	/// assert_eq!(vec.try_first_chunk_mut::<4>(), Ok(None));
	/// ```
	pub fn try_first_chunk_mut<const SIZE: usize>(&mut self) -> Result<Option<&mut [T; SIZE]>> {
		self.try_as_mut_slice().map(<[_]>::first_chunk_mut)
	}

	/// Returns a mutable reference to the last `SIZE` elements of the vector, or `None` if the
	/// vector contains less than `SIZE` elements.
	///
	/// # Errors
	///
	/// Returns an error if the vector contains at least `SIZE` elements but holds a shared
	/// reference to its buffer. If the vector contains less than `SIZE` elements, `None` is always
	/// returned.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([0, 1, 2]);
	///
	/// if let Ok(Some(last)) = vec.try_last_chunk_mut::<2>() {
	///     *last = [10, 20];
	/// }
	/// assert_eq!(vec, [0, 10, 20]);
	///
	/// assert_eq!(vec.try_last_chunk_mut::<4>(), Ok(None));
	/// ```
	pub fn try_last_chunk_mut<const SIZE: usize>(&mut self) -> Result<Option<&mut [T; SIZE]>> {
		self.try_as_mut_slice().map(<[_]>::last_chunk_mut)
	}

	/// Returns a mutable reference to the first `SIZE` elements and the remaining slice of the
	/// vector, or `None` if it is empty.
	///
	/// # Errors
	///
	/// Returns an error if the vector contains at least `SIZE` elements but holds a shared
	/// reference to its buffer. If the vector contains less than `SIZE` elements, `None` is always
	/// returned.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([0, 1, 2]);
	///
	/// if let Ok(Some((first, rest))) = vec.try_split_first_chunk_mut::<2>() {
	///     *first = [3, 4];
	///     rest[0] = 5;
	/// }
	/// assert_eq!(vec, [3, 4, 5]);
	///
	/// assert_eq!(vec.try_split_first_chunk_mut::<4>(), Ok(None));
	/// ```
	pub fn try_split_first_chunk_mut<const SIZE: usize>(&mut self) -> Result<Option<(&mut [T; SIZE], &mut [T])>> {
		self.try_as_mut_slice().map(<[_]>::split_first_chunk_mut)
	}

	/// Returns a mutable reference to the last `SIZE` elements and the remaining slice of the
	/// vector, or `None` if it is empty.
	///
	/// # Errors
	///
	/// Returns an error if the vector contains at least `SIZE` elements but holds a shared
	/// reference to its buffer. If the vector contains less than `SIZE` elements, `None` is always
	/// returned.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([0, 1, 2]);
	///
	/// if let Ok(Some((rest, last))) = vec.try_split_last_chunk_mut::<2>() {
	///     *last = [3, 4];
	///     rest[0] = 5;
	/// }
	/// assert_eq!(vec, [5, 3, 4]);
	///
	/// assert_eq!(vec.try_split_last_chunk_mut::<4>(), Ok(None));
	/// ```
	pub fn try_split_last_chunk_mut<const SIZE: usize>(&mut self) -> Result<Option<(&mut [T], &mut [T; SIZE])>> {
		self.try_as_mut_slice().map(<[_]>::split_last_chunk_mut)
	}

	/// Returns an element or subslice of the vector at an index, or `None` if the index is out of
	/// bounds.
	///
	/// # Errors
	///
	/// Returns an error if the index is within bounds but the vector holds a shared reference to
	/// its buffer. If the index is out of bounds, `None` is always returned.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([0, 1, 2]);
	///
	/// if let Ok(Some(elem)) = vec.try_get_mut(1) {
	///     *elem = 42;
	/// }
	/// assert_eq!(vec, [0, 42, 2]);
	///
	/// assert_eq!(vec.try_get_mut(3), Ok(None));
	/// ```
	pub fn try_get_mut<I>(&mut self, index: I) -> Result<Option<&mut I::Output>>
	where
		I: SliceIndex<[T]>
	{
		self.try_as_mut_slice().map(|slice| slice.get_mut(index))
	}

	/// Swaps two elements in the vector.
	///
	/// If both indexes are equal, the vector is not modified.
	///
	/// # Errors
	///
	/// Returns an error if the vector would be modified but holds a shared reference to its buffer.
	///
	/// # Panics
	///
	/// Panics if either index is out of bounds.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([1, 2, 3, 4, 5]);
	///
	/// assert!(vec.try_swap(1, 3).is_ok());
	/// assert_eq!(vec, [1, 4, 3, 2, 5]);
	/// ```
	pub fn try_swap(&mut self, i: usize, j: usize) -> Result {
		self.try_as_mut_slice()?.swap(i, j);
		Ok(())
	}

	/// Reverses the order of elements in the vector.
	///
	/// # Errors
	///
	/// Returns an error is the vector would be modified but holds a shared reference to its buffer.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([1, 2, 3]);
	/// assert!(vec.try_reverse().is_ok());
	/// assert_eq!(vec, [3, 2, 1]);
	/// ```
	pub fn try_reverse(&mut self) -> Result {
		self.try_as_mut_slice()?.reverse();
		Ok(())
	}

	/// Returns an iterator that yields mutable references to each element.
	///
	/// # Errors
	///
	/// Returns an error if the vector is not empty and holds a shared reference to its buffer.
	/// If the vector is empty, an empty iterator is always returned.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([1, 2, 4]);
	///
	/// if let Ok(iter) = vec.try_iter_mut() {
	///     for elem in iter {
	///         *elem += 2;
	///     }
	/// }
	/// assert_eq!(vec, [3, 4, 6]);
	/// ```
	pub fn try_iter_mut(&mut self) -> Result<IterMut<T>> {
		self.try_as_mut_slice().map(<[_]>::iter_mut)
	}

	/// Returns an iterator over `chunk_size` elements of the vector at a time, starting at the
	/// beginning of the vector.
	///
	/// The chunks are mutable slices, and do not overlap. If `chunk_size` does not divide the
	/// length of the vector, then the last chunk will not have length `chunk_size`.
	///
	/// See [`try_chunks_exact_mut`] for a variant of this iterator that returns chunks of exactly
	/// `chunk_size` elements, and [`try_rchunks_mut`] for the same iterator but starting at the end
	/// of the vector.
	///
	/// [`try_chunks_exact_mut`]: Self::try_chunks_exact_mut
	/// [`try_rchunks_mut`]: Self::try_rchunks_mut
	///
	/// # Errors
	///
	/// Returns an error if the vector is not empty and holds a shared reference to its buffer. If
	/// the vector is empty, an empty iterator is always returned.
	///
	/// # Panics
	///
	/// Panics if `chunk_size` is zero.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([0, 0, 0, 0, 0]);
	/// let mut count = 1;
	///
	/// if let Ok(chunks) = vec.try_chunks_mut(2) {
	///     for chunk in chunks {
	///         chunk.fill(count);
	///         count += 1;
	///     }
	/// }
	///
	/// assert_eq!(vec, [1, 1, 2, 2, 3]);
	/// ```
	pub fn try_chunks_mut(&mut self, chunk_size: usize) -> Result<ChunksMut<T>> {
		assert_ne!(chunk_size, 0, "chunk size must be non-zero");
		self.try_as_mut_slice().map(|slice| slice.chunks_mut(chunk_size))
	}

	/// Returns an iterator over `chunk_size` elements of the vector at a time, starting at the
	/// beginning of the vector.
	///
	/// The chunks are mutable slices, and do not overlap. If `chunk_size` does not divide the
	/// length of the vector, then the last up to `chunk_size - 1` elements will be omitted and can
	/// be retrieved from the `into_remainder` function of the iterator.
	///
	/// Due to each chunk having exactly `chunk_size` elements, the compiler can often optimize the
	/// resulting code better than in the case of [`try_chunks_mut`].
	///
	/// See [`try_chunks_mut`] for a variant of this iterator that also returns the remainder as a
	/// smaller chunk, and [`try_rchunks_exact_mut`] for the same iterator but starting at the end
	/// of the vector.
	///
	/// [`try_chunks_mut`]: Self::try_chunks_mut
	/// [`try_rchunks_exact_mut`]: Self::try_rchunks_exact_mut
	///
	/// # Errors
	///
	/// Returns an error if the vector is not empty and holds a shared reference to its buffer. If
	/// the vector is empty, an empty iterator is always returned.
	///
	/// # Panics
	///
	/// Panics if `chunk_size` is zero.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([0, 0, 0, 0, 0]);
	/// let mut count = 1;
	///
	/// if let Ok(chunks) = vec.try_chunks_exact_mut(2) {
	///     for chunk in chunks {
	///         chunk.fill(count);
	///         count += 1;
	///     }
	/// }
	///
	/// assert_eq!(vec, [1, 1, 2, 2, 0]);
	/// ```
	pub fn try_chunks_exact_mut(&mut self, chunk_size: usize) -> Result<ChunksExactMut<T>> {
		assert_ne!(chunk_size, 0, "chunk size must be non-zero");
		self.try_as_mut_slice().map(|slice| slice.chunks_exact_mut(chunk_size))
	}

	/// Returns an iterator over `chunk_size` elements of the vector at a time, starting at the end
	/// of the vector.
	///
	/// The chunks are mutable slices, and do not overlap. If `chunk_size` does not divide the
	/// length of the vector, then the last chunk will not have length `chunk_size`.
	///
	/// See [`try_rchunks_exact_mut`] for a variant of this iterator that returns chunks of exactly
	/// `chunk_size` elements, and [`try_chunks_mut`] for the same iterator but starting at the
	/// beginning of the vector.
	///
	/// [`try_rchunks_exact_mut`]: Self::try_rchunks_exact_mut
	/// [`try_chunks_mut`]: Self::try_chunks_mut
	///
	/// # Errors
	///
	/// Returns an error if the vector is not empty and holds a shared reference to its buffer. If
	/// the vector is empty, an empty iterator is always returned.
	///
	/// # Panics
	///
	/// Panics if `chunk_size` is zero.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([0, 0, 0, 0, 0]);
	/// let mut count = 1;
	///
	/// if let Ok(chunks) = vec.try_rchunks_mut(2) {
	///     for chunk in chunks {
	///         chunk.fill(count);
	///         count += 1;
	///     }
	/// }
	///
	/// assert_eq!(vec, [3, 2, 2, 1, 1]);
	/// ```
	pub fn try_rchunks_mut(&mut self, chunk_size: usize) -> Result<RChunksMut<T>> {
		assert_ne!(chunk_size, 0, "chunk size must be non-zero");
		self.try_as_mut_slice().map(|slice| slice.rchunks_mut(chunk_size))
	}

	/// Returns an iterator over `chunk_size` elements of the vector at a time, starting at the end
	/// of the vector.
	///
	/// The chunks are mutable slices, and do not overlap. If `chunk_size` does not divide the
	/// length of the vector, then the last up to `chunk_size - 1` elements will be omitted and can
	/// be retrieved from the `into_remainder` function of the iterator.
	///
	/// Due to each chunk having exactly `chunk_size` elements, the compiler can often optimize the
	/// resulting code better than in the case of [`try_chunks_mut`].
	///
	/// See [`try_rchunks_mut`] for a variant of this iterator that also returns the remainder as a
	/// smaller chunk, and [`try_chunks_exact_mut`] for the same iterator but starting at the
	/// beginning of the vector.
	///
	/// [`try_chunks_mut`]: Self::try_chunks_mut
	/// [`try_rchunks_mut`]: Self::try_rchunks_mut
	/// [`try_chunks_exact_mut`]: Self::try_chunks_exact_mut
	///
	/// # Errors
	///
	/// Returns an error if the vector is not empty and holds a shared reference to its buffer. If
	/// the vector is empty, an empty iterator is always returned.
	///
	/// # Panics
	///
	/// Panics if `chunk_size` is zero.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([0, 0, 0, 0, 0]);
	/// let mut count = 1;
	///
	/// if let Ok(chunks) = vec.try_rchunks_exact_mut(2) {
	///     for chunk in chunks {
	///         chunk.fill(count);
	///         count += 1;
	///     }
	/// }
	///
	/// assert_eq!(vec, [0, 2, 2, 1, 1]);
	/// ```
	pub fn try_rchunks_exact_mut(&mut self, chunk_size: usize) -> Result<RChunksExactMut<T>> {
		assert_ne!(chunk_size, 0, "chunk size must be non-zero");
		self.try_as_mut_slice().map(|slice| slice.rchunks_exact_mut(chunk_size))
	}

	// Todo: add `chunks_by_mut` and `rchunks_by_mut`, stabilized in 1.77?

	/// Divides the vector into two mutable slices at an index.
	///
	/// The first slice will contain all indices from `[0, mid)` (excluding the index `mid` itself)
	/// and the second will contain all indices from `[mid, len)` (excluding the index `len` itself).
	///
	/// # Errors
	///
	/// Returns an error if the vector is not empty and holds a shared reference to its buffer. If
	/// the vector is empty and `mid` is in bounds (i.e. it equals `0`), empty slices are always
	/// returned.
	///
	/// # Panics
	///
	/// Panics if `mid > len`.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([1, 0, 3, 0, 5, 6]);
	///
	/// if let Ok((left, right)) = vec.try_split_at_mut(2) {
	///     assert_eq!(left, [1, 0]);
	///     assert_eq!(right, [3, 0, 5, 6]);
	///     left[1] = 2;
	///     right[1] = 4;
	/// }
	///
	/// assert_eq!(vec, [1, 2, 3, 4, 5, 6]);
	/// ```
	pub fn try_split_at_mut(&mut self, mid: usize) -> Result<(&mut [T], &mut [T])> {
		assert!(mid <= self.len(), "midpoint out of bounds");
		self.try_as_mut_slice().map(|slice| slice.split_at_mut(mid))
	}

	// Todo: add `split_at_mut_checked`, stabilized in 1.80, and `split_at_mut_unchecked`, stabilized
	//  in 1.79

	/// Returns an iterator over mutable subslices separated by elements that match `pred`. The
	/// matched element is not contained in the subslices.
	///
	/// # Errors
	///
	/// Returns an error if the vector is not empty and holds a shared reference to its buffer. If
	/// the vector is empty, an empty iterator is always returned, and `pred` is not called.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([10, 40, 30, 20, 60, 50]);
	///
	/// if let Ok(groups) = vec.try_split_mut(|&num| num % 3 == 0) {
	///     for group in groups {
	///         group[0] = 1;
	///     }
	/// }
	///
	/// assert_eq!(vec, [1, 40, 30, 1, 60, 1]);
	/// ```
	pub fn try_split_mut<F>(&mut self, pred: F) -> Result<SplitMut<T, F>>
	where
		F: FnMut(&T) -> bool,
	{
		let slice = self.try_as_mut_slice()?;
		Ok(slice.split_mut(pred))
	}

	/// Returns an iterator over mutable subslices separated by elements that match `pred`. The
	/// matched element is contained in the previous subslice as a terminator.
	///
	/// # Errors
	///
	/// Returns an error if the vector is not empty and holds a shared reference to its buffer. If
	/// the vector is empty, an empty iterator is always returned, and `pred` is not called.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([10, 40, 30, 20, 60, 50]);
	///
	/// if let Ok(groups) = vec.try_split_inclusive_mut(|&num| num % 3 == 0) {
	///     for group in groups {
	///         let terminator_idx = group.len() - 1;
	///         group[terminator_idx] = 1;
	///     }
	/// }
	///
	/// assert_eq!(vec, [10, 40, 1, 20, 1, 1]);
	/// ```
	pub fn try_split_inclusive_mut<F>(&mut self, pred: F) -> Result<SplitInclusiveMut<T, F>>
	where
		F: FnMut(&T) -> bool,
	{
		let slice = self.try_as_mut_slice()?;
		Ok(slice.split_inclusive_mut(pred))
	}

	/// Returns an iterator over mutable subslices separated by elements that match `pred`, starting
	/// at the end of the vector and working backwards. The matched element is not contained in the
	/// subslices.
	///
	/// # Errors
	///
	/// Returns an error if the vector is not empty and holds a shared reference to its buffer. If
	/// the vector is empty, an empty iterator is always returned, and `pred` is not called.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([10, 40, 30, 20, 60, 50]);
	///
	/// if let Ok(groups) = vec.try_rsplit_mut(|&num| num % 3 == 0) {
	///     for group in groups {
	///         group[0] = 1;
	///     }
	/// }
	/// assert_eq!(vec, [1, 40, 30, 1, 60, 1]);
	/// ```
	pub fn try_rsplit_mut<F>(&mut self, pred: F) -> Result<RSplitMut<T, F>>
	where
		F: FnMut(&T) -> bool,
	{
		let slice = self.try_as_mut_slice()?;
		Ok(slice.rsplit_mut(pred))
	}

	/// Returns an iterator over mutable subslices separated by elements that match `pred`, limited
	/// to returning at most `n` items. The matched element is not contained in the subslices.
	///
	/// The last element returned, if any, will contain the remainder of the vector.
	///
	/// # Errors
	///
	/// Returns an error if the vector is not empty and holds a shared reference to its buffer. If
	/// the vector is empty, an empty iterator is always returned, and `pred` is not called.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([10, 40, 30, 20, 60, 50]);
	///
	/// if let Ok(groups) = vec.try_splitn_mut(2, |&num| num % 3 == 0) {
	///     for group in groups {
	///         group[0] = 1;
	///     }
	/// }
	///
	/// assert_eq!(vec, [1, 40, 30, 1, 60, 50]);
	/// ```
	pub fn try_splitn_mut<F>(&mut self, n: usize, pred: F) -> Result<SplitNMut<T, F>>
	where
		F: FnMut(&T) -> bool,
	{
		let slice = self.try_as_mut_slice()?;
		Ok(slice.splitn_mut(n, pred))
	}

	/// Returns an iterator over subslices separated by elements that match `pred` limited to
	/// returning at most `n` items. This starts at the end of the vector and works backwards. The
	/// matched element is not contained in the subslices.
	///
	/// The last element returned, if any, will contain the remainder of the vector.
	///
	/// # Errors
	///
	/// Returns an error if the vector is not empty and holds a shared reference to its buffer. If
	/// the vector is empty, an empty iterator is always returned, and `pred` is not called.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([10, 40, 30, 20, 60, 50]);
	///
	/// if let Ok(groups) = vec.try_rsplitn_mut(2, |&num| num % 3 == 0) {
	///     for group in groups {
	///         group[0] = 1;
	///     }
	/// }
	///
	/// assert_eq!(vec, [1, 40, 30, 20, 60, 1]);
	/// ```
	pub fn try_rsplitn_mut<F>(&mut self, n: usize, pred: F) -> Result<RSplitNMut<T, F>>
	where
		F: FnMut(&T) -> bool,
	{
		let slice = self.try_as_mut_slice()?;
		Ok(slice.rsplitn_mut(n, pred))
	}

	// Todo: add `sort_unstable`, `select_nth_unstable`, etc., and `sort`, `sort_by`, etc. which
	//  allocate intermediate memory.

	/// Rotates the vector in-place such that the first `mid` elements of the vector move to the end
	/// while the last `len - mid` elements move to the start.
	///
	/// After calling `rotate_left`, the element previously at index `mid` will become the first
	/// element in the vector.
	///
	/// # Errors
	///
	/// Returns an error if the vector is not empty and holds a shared reference to its buffer. If
	/// the vector is empty and `mid` is in bounds (i.e. it equals `0`), [`Ok`] is always returned.
	///
	/// # Panics
	///
	/// This function will panic if `mid` is greater than the length of the vector. Note that
	/// `mid == len` does _not_ panic and is a no-op rotation.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<char> = Vec::from(['a', 'b', 'c', 'd', 'e', 'f']);
	/// assert!(vec.try_rotate_left(2).is_ok());
	/// assert_eq!(vec, ['c', 'd', 'e', 'f', 'a', 'b']);
	/// ```
	pub fn try_rotate_left(&mut self, mid: usize) -> Result {
		assert!(mid <= self.len(), "midpoint out of bounds");
		let slice = self.try_as_mut_slice()?;
		slice.rotate_left(mid);
		Ok(())
	}

	/// Rotates the vector in-place such that the first `len - k` elements of the vector move to the
	/// end while the last `k` elements move to the start.
	///
	/// After calling `rotate_right`, the element previously at index `len - k` will become the
	/// first element in the vector.
	///
	/// # Errors
	///
	/// Returns an error if the vector is not empty and holds a shared reference to its buffer. If
	/// the vector is empty and `k` is in bounds (i.e. it equals `0`), [`Ok`] is always returned.
	///
	/// # Panics
	///
	/// This function will panic if `k` is greater than the length of the vector. Note that
	/// `k == len` does _not_ panic and is a no-op rotation.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<char> = Vec::from(['a', 'b', 'c', 'd', 'e', 'f']);
	/// assert!(vec.try_rotate_right(2).is_ok());
	/// assert_eq!(vec, ['e', 'f', 'a', 'b', 'c', 'd']);
	/// ```
	pub fn try_rotate_right(&mut self, k: usize) -> Result {
		assert!(k <= self.len(), "midpoint out of bounds");
		let slice = self.try_as_mut_slice()?;
		slice.rotate_right(k);
		Ok(())
	}

	/// Fills the current vector length by cloning `value`.
	///
	/// # Errors
	///
	/// Returns an error if the vector is not empty and holds a shared reference to its buffer. If
	/// the vector is empty, [`Ok`] is always returned.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([0; 8]);
	/// assert!(vec.try_fill(1).is_ok());
	/// assert_eq!(vec, [1; 8]);
	/// ```
	pub fn try_fill(&mut self, value: T) -> Result
	where
		T: Clone,
	{
		// Todo: Don't defer to <[T]>::fill because `clone` could panic, cluttering
		//  the stacktrace.
		let slice = self.try_as_mut_slice()?;
		slice.fill(value);
		Ok(())
	}

	/// Fills the current vector length with elements returned by calling a closure repeatedly.
	///
	/// This method uses a closure to create new values. If you'd rather [`Clone`] a given value,
	/// use [`try_fill`]. If you want to use the [`Default`] trait to generate values, you can pass
	/// [`Default::default`] as the argument.
	///
	/// [`try_fill`]: Self::try_fill
	///
	/// # Errors
	///
	/// Returns an error if the vector is not empty and holds a shared reference to its buffer. If
	/// the vector is empty, [`Ok`] is always returned and the `fill` closure is never called.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([1; 8]);
	/// assert!(vec.try_fill_with(Default::default).is_ok());
	/// assert_eq!(vec, [0; 10]);
	/// ```
	pub fn try_fill_with<F>(&mut self, mut fill: F) -> Result
	where
		F: FnMut() -> T,
	{
		// Don't defer to <[T]>::fill_with because the closure could panic, and it
		// isn't marked `#[track_caller]`.
		for elem in self.try_iter_mut()? {
			*elem = fill();
		}
		Ok(())
	}
}

// CoW operations
impl<T: Clone, A: Allocator + Clone, const ATOMIC: bool> Vec<T, ATOMIC, A> {
	/// Returns a mutable slice over the vector contents, cloning out of a shared allocation.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([1, 2, 3]);
	/// let clone = vec.clone();
	///
	/// let slice = vec.as_mut_slice();
	/// for v in slice {
	///     *v *= 2;
	/// }
	///
	/// assert_eq!(vec, [2, 4, 6]);
	/// // The first vector's contents have been cloned and are no longer shared
	/// // with the second.
	/// assert_ne!(vec, clone);
	/// ```
	pub fn as_mut_slice(&mut self) -> &mut [T] {
		todo!()
	}
	
	/// Returns the remaining spare capacity of the vector as a slice of uninitialized elements,
	/// cloning out of a shared allocation.
	///
	/// The returned slice can be used to fill the vector, before marking the data as initialized
	/// with [`set_len`].
	///
	/// To return an error if the vector is shared, without allocating or cloning, use
	/// [`try_spare_capacity_mut`] instead.
	///
	/// [`set_len`]: Self::set_len
	/// [`try_spare_capacity_mut`]: Self::try_spare_capacity_mut
	///
	/// # Panics
	///
	/// Panics if allocation fails, for example in an out-of-memory condition.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::with_capacity(3);
	///
	/// let spare = vec.spare_capacity_mut();
	/// spare[0].write(0);
	/// spare[1].write(1);
	/// spare[2].write(2);
	///
	/// unsafe {
	///     vec.set_len(3);
	/// }
	///
	/// assert_eq!(vec, [0, 1, 2]);
	/// ```
	pub fn spare_capacity_mut(&mut self) -> &mut [MaybeUninit<T>] {
		todo!()
	}

	/// Clones the vector contents out of a shared allocation, making the vector mutable.
	/// Returns an "always-mutable" view into the vector.
	///
	/// Any weak references are disassociated from the contents without cloning. See the note on
	/// [`Unique`] for details.
	///
	/// To return an error if the vector is shared, without allocating or cloning, use [`unique`]
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
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([1, 2, 3]);
	/// let clone = vec.clone();
	///
	/// let mut unique = vec.as_unique();
	/// unique.clear();
	/// unique.extend_from_slice(&[4, 5, 6]);
	/// assert!(vec.is_unique());
	/// assert_eq!(vec, [4, 5, 6]);
	///
	/// // The first vector's contents have been cloned and are no longer shared
	/// // with the second.
	/// assert!(clone.is_unique());
	/// assert_ne!(vec, clone);
	/// ```
	pub fn as_unique(&mut self) -> Unique<T, A, ATOMIC> {
		todo!()
	}

	/// Clones the vector contents out of a [shared] allocation, making the vector mutable. Returns
	/// an "always-mutable" view into the vector.
	///
	/// Any weak references are disassociated from the contents without cloning. See the note on
	/// [`Unique`] for details.
	///
	/// To return an error if the vector is shared, without allocating or cloning, use [`unique`]
	/// instead.
	///
	/// [shared]: Self::is_shared
	/// [`unique`]: Self::unique
	///
	/// # Errors
	///
	/// Returns an error if allocation fails, for example in an out-of-memory condition.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([1, 2, 3]);
	/// let clone = vec.clone();
	///
	/// let mut unique = vec.try_as_unique().expect("allocation failed");
	/// unique.clear();
	/// unique.extend_from_slice(&[4, 5, 6]);
	/// assert!(vec.is_unique());
	/// assert_eq!(vec, [4, 5, 6]);
	///
	/// // The first vector's contents have been cloned and are no longer shared
	/// // with the second.
	/// assert!(clone.is_unique());
	/// assert_ne!(vec, clone);
	/// ```
	pub fn try_as_unique(&mut self) -> Result<Unique<T, A, ATOMIC>, AllocError> {
		todo!()
	}
	
	/// Reserves space for at least `additional` elements, cloning out of a shared reference. The
	/// vector may reserve more space to speculatively avoid frequent reallocations. The reserved
	/// capacity will be greater than or equal to `length + additional`. No memory is allocated if
	/// the capacity is already sufficient.
	///
	/// To return an error if the vector is shared without cloning, use [`try_reserve`] instead.
	///
	/// [`try_reserve`]: Self::try_reserve
	///
	/// # Panics
	///
	/// Panics if the new capacity is greater than [`isize::MAX`] *bytes* minus three [`usize`]
	/// words.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([1]);
	/// vec.reserve(10);
	/// assert!(vec.capacity() >= 11);
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
	/// The allocator may give the vector more space than it requests. Therefore, capacity cannot be
	/// relied upon to be precisely minimal. [`reserve`] is preferred if future insertions are
	/// expected.
	///
	/// To return an error if the vector is shared without cloning, use [`try_reserve_exact`]
	/// instead.
	///
	/// [`try_reserve`]: Self::try_reserve
	/// [`reserve`]: Self::reserve
	/// [`reserve_exact`]: Self::reserve_exact
	///
	/// # Panics
	///
	/// Panics if the new capacity is greater than [`isize::MAX`] *bytes* minus three [`usize`]
	/// words.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([1]);
	/// vec.reserve_exact(10);
	/// assert!(vec.capacity() >= 11);
	/// ```
	pub fn reserve_exact(&mut self, additional: usize) {
		todo!()
	}

	// Todo: try_reserve with errors instead of panics, similar to Vec::try_reserve?

	/// Shrinks the capacity of the vector as much as possible, cloning out of a shared reference.
	///
	/// The behavior of this method depends on the allocator, which may either shrink the vector
	/// in-place or reallocate. The resulting vector might still have some excess capacity, just as
	/// is the case for [`with_capacity`]. See [`Allocator::shrink`] for more details.
	///
	/// To return an error if the vector is shared without cloning, use [`try_shrink_to_fit`]
	/// instead.
	///
	/// [`with_capacity`]: Self::with_capacity
	/// [`try_shrink_to_fit`]: Self::try_shrink_to_fit
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::with_capacity(10);
	/// vec.extend([1, 2, 3]);
	/// assert!(vec.capacity() >= 10);
	/// vec.shrink_to_fit();
	/// assert!(vec.capacity() >= 3);
	/// ```
	pub fn shrink_to_fit(&mut self) {
		todo!()
	}

	/// Shrinks the capacity of the vector with a lower bound.
	///
	/// The capacity will be at least as large as both the length and the supplied value. If the
	/// current capacity is less than the lower limit, this does nothing.
	///
	/// To return an error if the vector is shared without cloning, use [`try_shrink_to`] instead.
	/// 
	/// [`try_shrink_to`]: Self::try_shrink_to
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::with_capacity(10);
	/// vec.extend([1, 2, 3]);
	/// assert!(vec.capacity() >= 10);
	/// vec.shrink_to(4);
	/// assert!(vec.capacity() >= 4);
	/// vec.shrink_to(0);
	/// assert!(vec.capacity() >= 3);
	/// ```
	pub fn shrink_to(&mut self, min_capacity: usize) {
		todo!()
	}

	/// Removes and returns the element at position `index` from the vector, replacing this element
	/// with the last element in the vector. This doesn't preserve ordering of the remaining
	/// elements, but is *O*(1) for unique vectors. If ordering must be preserved, use [`remove`].
	///
	/// If the vector is shared, its contents will be cloned into a unique allocation. A fallible
	/// version is also provided: [`try_swap_remove`].
	///
	/// [`remove`]: Self::remove
	/// [`try_swap_remove`]: Self::try_swap_remove
	///
	/// # Panics
	///
	/// Panics if `index` is greater than the vector length.
	///
	/// # Time complexity
	///
	/// Takes *O*(1) time if the vector reference is unique, *O*(*n*) if shared.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec = Vec::from(['a', 'b', 'c', 'd']);
	///
	/// assert_eq!(vec.swap_remove(1), 'b');
	/// assert_eq!(vec, ['a', 'd', 'c']);
	///
	/// assert_eq!(vec.swap_remove(0), 'a');
	/// assert_eq!(vec, ['c', 'd']);
	/// ```
	pub fn swap_remove(&mut self, index: usize) -> T {
		todo!()
	}

	/// Removes and returns the element at position `index` from the vector, shifting all subsequent
	/// elements to the left.
	///
	/// If the vector is shared, its contents will be cloned into a unique allocation. A fallible
	/// version is also provided: [`try_remove`].
	///
	/// [`try_remove`]: Self::try_remove
	///
	/// # Panics
	///
	/// Panics if `index` is greater than the vector length.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec = Vec::from(['a', 'b', 'c']);
	/// assert_eq!(vec.remove(1), 'b');
	/// assert_eq!(vec, ['a', 'c']);
	/// ```
	///
	/// # Time complexity
	///
	/// For unique vectors, takes at most *O*(*n*) time, as all elements after `index` must be
	/// shifted. In the worst case, all [`len`] elements must be shifted when `index` is `0`. If
	/// element ordering is not important, use [`swap_remove`] instead, which is *O*(1) for unique
	/// vectors. If you need to remove elements from the beginning of the vector frequently and need
	/// to preserve ordering, consider [`ArrayDeque::pop_front`], which is also *O*(1).
	///
	/// Always takes *O*(*n*) time for shared vectors.
	///
	/// [`len`]: Self::len
	/// [`swap_remove`]: Self::swap_remove
	/// [`ArrayDeque::pop_front`]: crate::array::deque::ArrayDeque::pop_front
	pub fn remove(&mut self, index: usize) -> T {
		todo!()
	}

	/// Inserts an element at position `index` within the vector, shifting all subsequent elements to
	/// the right.
	///
	/// If the vector is shared, its contents will be cloned into a unique allocation. A fallible
	/// version is also provided: [`try_insert`].
	///
	/// [`try_insert`]: Self::try_insert
	///
	/// # Panics
	///
	/// Panics if `index` is greater than the vector length.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec = Vec::from(['a', 'c']);
	///
	/// vec.insert(1, 'b');
	/// assert_eq!(vec, ['a', 'b', 'c']);
	/// vec.insert(3, 'd');
	/// assert_eq!(vec, ['a', 'b', 'c', 'd']);
	/// ```
	///
	/// # Time complexity
	///
	/// For unique vectors, takes at most *O*(*n*) time, as all elements after `index` must be
	/// shifted. In the worst case, all [`len`] elements must be shifted when `index` is `0`.
	///
	/// Always takes *O*(*n*) time for shared vectors.
	///
	/// [`len`]: Self::len
	pub fn insert(&mut self, index: usize, element: T) {
		todo!()
	}

	/// Retains the elements specified by `predicate`, dropping the rest.
	///
	/// Removes all elements `e` for which `predicate(&e)` returns `false`. This method operates
	/// in-place, visiting each element exactly once in the original order, and preserves the order
	/// of the retained elements.
	///
	/// If the vector is shared, its contents will be cloned into a unique allocation. A fallible
	/// version is also provided: [`try_retain`].
	///
	/// [`try_retain`]: Self::try_retain
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([1, 2, 3, 4]);
	/// vec.retain(|&x| x % 2 == 0);
	/// assert_eq!(vec, [2, 4]);
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
	/// If the vector is shared, its contents will be cloned into a unique allocation. A fallible
	/// version is also provided: [`try_retain_mut`].
	///
	/// [`try_retain_mut`]: Self::try_retain_mut
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([1, 2, 3, 4]);
	/// vec.retain_mut(|x| if *x % 2 == 0 {
	///     *x += 1;
	///     true
	/// } else {
	///     false
	/// });
	/// assert_eq!(vec, [3, 5]);
	/// ```
	pub fn retain_mut<F: FnMut(&mut T) -> bool>(&mut self, predicate: F) {
		todo!()
	}

	/// Removes consecutive repeated elements from the vector according to the [`PartialEq`] trait
	/// implementation. If the vector is sorted, all duplicates are removed.
	///
	/// If the vector is shared, its contents will be cloned into a unique allocation. A fallible
	/// version is also provided: [`try_dedup`].
	///
	/// [`try_dedup`]: Self::try_dedup
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([1, 2, 2, 3, 2]);
	/// vec.dedup();
	/// assert_eq!(vec, [1, 2, 3, 2]);
	/// ```
	pub fn dedup(&mut self) where T: PartialEq {
		todo!()
	}
	/// Removes consecutive repeated elements from the vector that resolve to the same key given by
	/// `key`. If the vector is sorted, all duplicates are removed.
	///
	/// If the vector is shared, its contents will be cloned into a unique allocation. A fallible
	/// version is also provided: [`try_dedup_by_key`].
	///
	/// [`try_dedup_by_key`]: Self::try_dedup_by_key
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([10, 20, 21, 30, 20]);
	/// vec.dedup_by_key(|&mut x| x / 10);
	/// assert_eq!(vec, [10, 20, 30, 20]);
	/// ```
	pub fn dedup_by_key<F: FnMut(&mut T) -> K, K: PartialEq>(&mut self, key: F) {
		todo!()
	}
	/// Removes consecutive repeated elements from the vector that satisfy an equality `predicate`.
	/// If the vector is sorted, all duplicates are removed.
	///
	/// The `predicate` function is passed references to two elements from the vector and determines
	/// if the elements are equal. The elements are passed in opposite order, such that if
	/// `predicate(a, b)` returns `true`, element `a` is removed.
	///
	/// If the vector is shared, its contents will be cloned into a unique allocation. A fallible
	/// version is also provided: [`try_dedup_by`].
	///
	/// [`try_dedup_by`]: Self::try_dedup_by
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<char> = Vec::from(['a', 'A', 'b', 'c', 'c', 'B']);
	/// vec.dedup_by(|a, b| a.eq_ignore_ascii_case(b));
	/// assert_eq!(vec, ['a', 'b', 'c', 'B']);
	/// ```
	pub fn dedup_by<F: FnMut(&mut T, &mut T) -> bool>(&mut self, predicate: F) {
		todo!()
	}

	/// Appends an element to the end of the vector.
	///
	/// If the vector is shared, its contents will be cloned into a unique allocation. A fallible
	/// version is also provided: [`try_push`].
	///
	/// [`try_push`]: Self::try_push
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::new();
	/// vec.push(1);
	/// vec.push(2);
	/// vec.push(3);
	/// assert_eq!(vec, [1, 2, 3]);
	/// ```
	///
	/// # Time complexity
	///
	/// Takes *O*(1) time for unique vectors, *O*(*n*) time for shared vectors.
	pub fn push(&mut self, value: T) {
		todo!()
	}

	/// Moves all elements from `other` into the vector, leaving `other` empty. Any like[^atomic]
	/// vector type from this crate may be appended, even array vectors with a different fixed
	/// capacity.
	///
	/// If one vector is shared, its elements are cloned into the unique one. If both are shared,
	/// their contents will be cloned into a unique allocation. A fallible version is also provided:
	/// [`try_append`].
	///
	/// [^atomic]: the only restriction is that both vectors must either be atomic or non-atomic;
	/// atomic vectors may be only appended to other atomic vectors, non-atomic vectors may only be
	/// appended to other non-atomic vectors.
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
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec1: Vec<i32> = Vec::from([1, 2, 3]);
	/// let mut vec2 = Vec::from([4, 5, 6]);
	/// vec1.append(&mut vec2);
	/// assert_eq!(vec1, [1, 2, 3, 4, 5, 6]);
	/// assert_eq!(vec2, []);
	/// ```
	pub fn append<V: RcVector<T, A, ATOMIC> + ?Sized>(&mut self, other: &mut V) {
		todo!()
	}

	/// Removes the specified range from the vector, returning all removed elements as an iterator.
	/// If the iterator is dropped before being fully consumed, the remaining removed elements are
	/// dropped.
	///
	/// If range is not empty and the vector is shared, the kept elements will be cloned into a
	/// unique allocation before draining, and returned elements will be cloned out of the shared
	/// vector. A fallible version is also provided: [`try_drain`].
	///
	/// [`try_drain`]: Self::try_drain
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
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([1, 2, 3, 4, 5, 6, 7, 8]);
	/// let removed = vec.drain(2..6);
	/// assert!(removed.eq([3, 4, 5, 6]));
	/// assert_eq!(vec, [1, 2, 7, 8]);
	/// ```
	pub fn drain<R: RangeBounds<usize>>(&mut self, range: R) -> Drain<T, A, ATOMIC> {
		todo!()
	}

	/// Splits the vector into two at the given index.
	///
	/// Returns a new vector containing the elements starting from the given index. The original is
	/// left containing the elements up to `at` (exclusive).
	///
	/// - If you want to take ownership of the entire contents and capacity of the vector, use
	///   [`mem::take`] or [`mem::replace`].
	/// - If you don't need the returned vector at all, see [`truncate`].
	/// - If you want to take ownership of an arbitrary range, or you don't necessarily want to
	///   store the removed items, see [`drain`].
	///
	/// If the vector is shared, the elements after `at` are cloned into the returned vector. A
	/// fallible version is also provided: [`try_split_off`].
	///
	/// [`mem::take`]: core::mem::take
	/// [`mem::replace`]: core::mem::replace
	/// [`truncate`]: Self::truncate
	/// [`drain`]: Self::drain
	/// [`try_split_off`]: Self::try_split_off
	///
	/// # Leaking
	///
	/// Because memory may be shared and each shared vector may have a different length, this operation
	/// may cause the elements in the original vector after `at` to go out of scope without dropping.
	/// The element's [`Drop`] implementation can only be safely called when the vector holds a unique
	/// reference.
	///
	/// Rust does not require [`Drop::drop`] to be called, but this may be undesirable behavior for
	/// types with a non-trivial `drop` implementation. For such types, use [`unique`]/[`as_unique`]
	/// to get a mutable view which is guaranteed to drop elements, or [`is_unique`] to check for a
	/// unique reference.
	///
	/// [`unique`]: Self::unique
	/// [`as_unique`]: Self::as_unique
	/// [`is_unique`]: Self::is_unique
	///
	/// # Panics
	///
	/// Panics if `at` is greater than the vector length.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec = Vec::from([1, 2, 3, 4]);
	/// assert_eq!(vec.split_off(2), [3, 4]);
	/// assert_eq!(vec, [1, 2]);
	/// ```
	#[must_use = "use `.truncate()` if you don't need the other half"]
	pub fn split_off(&mut self, at: usize) -> Self {
		todo!()
	}

	/// Resizes the vector in-place to the specified length.
	///
	/// If `new_len` is greater than the current length, the vector is extended, filling the
	/// additional space with element returned from calling the closure `fill`. If `new_len` is less
	/// than the current length, the vector is truncated.
	///
	/// To fill the additional space by [`Clone`]ing a given value, use [`resize`]. To fill with
	/// default values, pass [`Default::default`] as the second argument.
	///
	/// If the vector is shared but must be extended, its contents are first cloned into a unique
	/// allocation before new elements are added.
	///
	/// [`resize`]: Self::resize
	///
	/// # Leaking
	///
	/// If the vector is truncated, the same leaking caveats as [`truncate`] apply.
	///
	/// [`truncate`]: Self::truncate#leaking
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([1, 2, 3]);
	/// let fill = Default::default;
	///
	/// vec.resize_with(5, fill);
	/// assert_eq!(vec, [1, 2, 3, 0, 0]);
	/// vec.resize_with(3, fill);
	/// assert_eq!(vec, [1, 2, 3]);
	/// ```
	pub fn resize_with<F: FnMut() -> T>(&mut self, new_len: usize, fill: F) {
		todo!()
	}

	/// Resizes the vector in-place to the specified length, cloning `value` into additional space
	/// as needed.
	///
	/// If the vector is shared but must be extended, its contents are first cloned into a unique
	/// allocation before new elements are added.
	///
	/// # Leaking
	///
	/// If the vector is truncated, the same leaking caveats as [`truncate`] apply.
	///
	/// [`truncate`]: Self::truncate#leaking
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([1, 2, 3]);
	///
	/// vec.resize(5, 0);
	/// assert_eq!(vec, [1, 2, 3, 0, 0]);
	/// vec.resize(3, 0);
	/// assert_eq!(vec, [1, 2, 3]);
	/// ```
	pub fn resize(&mut self, new_len: usize, value: T) {
		todo!()
	}

	/// Clones and appends all elements in a slice to the vector.
	///
	/// If the vector is shared, its contents are cloned into a unique allocation.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::new();
	/// vec.extend_from_slice(&[1, 2, 3]);
	/// assert_eq!(vec, [1, 2, 3, 4]);
	/// ```
	pub fn extend_from_slice(&mut self, other: &[T]) {
		todo!()
	}
	/// Clones and appends elements from `range` to the end of the vector.
	///
	/// If the vector is shared, its contents are cloned into a unique allocation.
	///
	/// # Panics
	///
	/// Panics if the start of the range is greater than the end or if the end of the range is
	/// greater than the length of the vector.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([1, 2, 3, 4]);
	/// vec.extend_from_within(1..3);
	/// assert_eq!(vec, [1, 2, 3, 4, 2, 3]);
	/// ```
	pub fn extend_from_within<R: RangeBounds<usize>>(&mut self, range: R) {
		todo!()
	}
}

impl<T: Clone, A: Allocator, const ATOMIC: bool> Vec<T, ATOMIC, A> {
	/// Removes and returns the last element from the vector, or [`None`] if it is empty. Clones the
	/// element out of a shared reference.
	///
	/// # Leaking
	///
	/// Because memory may be shared and each shared vector may have a different length, this operation
	/// may cause the removed element to go out of scope without dropping. The element's [`Drop`]
	/// implementation can only be safely called when the vector holds a unique reference.
	///
	/// Rust does not require [`Drop::drop`] to be called, but this may be undesirable behavior for
	/// types with a non-trivial `drop` implementation. For such types, use [`unique`]/[`as_unique`]
	/// to get a mutable view which is guaranteed to drop elements, or [`is_unique`] to check for a
	/// unique reference.
	///
	/// [`unique`]: Self::unique
	/// [`as_unique`]: Self::as_unique
	/// [`is_unique`]: Self::is_unique
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([1, 2]);
	/// assert_eq!(vec.pop(), Some(2));
	/// assert_eq!(vec.pop(), Some(1));
	/// assert_eq!(vec.pop(), None);
	/// ```
	pub fn pop(&mut self) -> Option<T> {
		todo!()
	}

	/// Removes and returns the last element from the vector if the predicate returns `true`, or
	/// `None` if predicate returns `false` or the vector is empty. If the vector is empty, the
	/// predicate is not called.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([1, 2, 3, 4]);
	/// let even = |x: &mut i32| *x % 2 == 0;
	/// assert_eq!(vec.pop_if(even), Some(4));
	/// assert_eq!(vec, [1, 2, 3]);
	/// assert_eq!(vec.pop_if(even), None);
	/// ```
	///
	/// # Time complexity
	///
	/// Takes *O*(1) time.
	pub fn pop_if<F: FnOnce(&mut T) -> bool>(&mut self, predicate: F) -> Option<T> {
		todo!()
	}
}

// CoW mutable slice operations
impl<T: Clone, A: Allocator + Clone, const ATOMIC: bool> Vec<T, ATOMIC, A> {
	/// Returns a mutable reference to the first element of the vector, or `None` if it is empty.
	///
	/// If the vector holds a shared reference, its contents are cloned into a unique allocation. To
	/// return an error if the vector is shared, without allocating or cloning, use [`try_first_mut`]
	/// instead.
	///
	/// [`try_first_mut`]: Self::try_first_mut
	///
	/// # Panics
	///
	/// Panics if allocation fails, for example in an out-of-memory condition.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([0, 1, 2]);
	///
	/// if let Some(first) = vec.first_mut() {
	///     *first = 5;
	/// }
	/// assert_eq!(vec, [5, 1, 2]);
	///
	/// vec.clear();
	/// assert_eq!(vec.first_mut(), None);
	/// ```
	pub fn first_mut(&mut self) -> Option<&mut T> {
		self.as_mut_slice().first_mut()
	}

	/// Returns a mutable reference to the last element of the vector, or `None` if it is empty.
	///
	/// If the vector holds a shared reference, its contents are cloned into a unique allocation. To
	/// return an error if the vector is shared, without allocating or cloning, use [`try_last_mut`]
	/// instead.
	///
	/// [`try_last_mut`]: Self::try_last_mut
	///
	/// # Panics
	///
	/// Panics if allocation fails, for example in an out-of-memory condition.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([0, 1, 2]);
	///
	/// if let Some(last) = vec.last_mut() {
	///     *last = 5;
	/// }
	/// assert_eq!(vec, [0, 1, 5]);
	///
	/// vec.clear();
	/// assert_eq!(vec.last_mut(), None);
	/// ```
	pub fn last_mut(&mut self) -> Option<&mut T> {
		self.as_mut_slice().last_mut()
	}

	/// Returns a mutable reference to the first element and the remaining slice of the vector, or
	/// `None` if it is empty.
	///
	/// If the vector holds a shared reference, its contents are cloned into a unique allocation. To
	/// return an error if the vector is shared, without allocating or cloning, use
	/// [`try_split_first_mut`] instead.
	///
	/// [`try_split_first_mut`]: Self::try_split_first_mut
	///
	/// # Panics
	///
	/// Panics if allocation fails, for example in an out-of-memory condition.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([0, 1, 2]);
	///
	/// if let Some((first, rest)) = vec.split_first_mut() {
	///     *first = 3;
	///     rest[0] = 4;
	///     rest[1] = 5;
	/// }
	/// assert_eq!(vec, [3, 4, 5]);
	///
	/// vec.clear();
	/// assert_eq!(vec.split_first_mut(), None);
	/// ```
	pub fn split_first_mut(&mut self) -> Option<(&mut T, &mut [T])> {
		self.as_mut_slice().split_first_mut()
	}

	/// Returns a mutable reference to the last element and the remaining slice of the vector, or
	/// `None` if it is empty.
	///
	/// If the vector holds a shared reference, its contents are cloned into a unique allocation. To
	/// return an error if the vector is shared, without allocating or cloning, use
	/// [`try_split_last_mut`] instead.
	///
	/// [`try_split_last_mut`]: Self::try_split_last_mut
	///
	/// # Panics
	///
	/// Panics if allocation fails, for example in an out-of-memory condition.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([0, 1, 2]);
	///
	/// if let Some((last, rest)) = vec.split_last_mut() {
	///     *last = 3;
	///     rest[0] = 4;
	///     rest[1] = 5;
	/// }
	/// assert_eq!(vec, [4, 5, 3]);
	///
	/// vec.clear();
	/// assert_eq!(vec.split_last_mut(), None);
	/// ```
	pub fn split_last_mut(&mut self) -> Option<(&mut T, &mut [T])> {
		self.as_mut_slice().split_last_mut()
	}

	/// Returns a mutable reference to the first `SIZE` elements of the vector, or `None` if the
	/// vector contains less than `SIZE` elements.
	///
	/// If the vector holds a shared reference, its contents are cloned into a unique allocation. To
	/// return an error if the vector is shared, without allocating or cloning, use
	/// [`try_first_chunk_mut`] instead.
	///
	/// [`try_first_chunk_mut`]: Self::try_first_chunk_mut
	///
	/// # Panics
	///
	/// Panics if allocation fails, for example in an out-of-memory condition.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([0, 1, 2]);
	///
	/// if let Some(first) = vec.first_chunk_mut::<2>() {
	///     *first = [5, 4];
	/// }
	/// assert_eq!(vec, [5, 4, 2]);
	///
	/// assert_eq!(vec.first_chunk_mut::<4>(), None);
	/// ```
	pub fn first_chunk_mut<const SIZE: usize>(&mut self) -> Option<&mut [T; SIZE]> {
		self.as_mut_slice().first_chunk_mut()
	}

	/// Returns a mutable reference to the last `SIZE` elements of the vector, or `None` if the
	/// vector contains less than `SIZE` elements.
	///
	/// If the vector holds a shared reference, its contents are cloned into a unique allocation. To
	/// return an error if the vector is shared, without allocating or cloning, use
	/// [`try_last_chunk_mut`] instead.
	///
	/// [`try_last_chunk_mut`]: Self::try_last_chunk_mut
	///
	/// # Panics
	///
	/// Panics if allocation fails, for example in an out-of-memory condition.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([0, 1, 2]);
	///
	/// if let Some(last) = vec.last_chunk_mut::<2>() {
	///     *last = [10, 20];
	/// }
	/// assert_eq!(vec, [0, 10, 20]);
	///
	/// assert_eq!(vec.last_chunk_mut::<4>(), None);
	/// ```
	pub fn last_chunk_mut<const SIZE: usize>(&mut self) -> Option<&mut [T; SIZE]> {
		self.as_mut_slice().last_chunk_mut()
	}

	/// Returns a mutable reference to the first `SIZE` elements and the remaining slice of the
	/// vector, or `None` if it is empty.
	///
	/// If the vector holds a shared reference, its contents are cloned into a unique allocation. To
	/// return an error if the vector is shared, without allocating or cloning, use
	/// [`try_split_first_chunk_mut`] instead.
	///
	/// [`try_split_first_chunk_mut`]: Self::try_split_first_chunk_mut
	///
	/// # Panics
	///
	/// Panics if allocation fails, for example in an out-of-memory condition.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([0, 1, 2]);
	///
	/// if let Some((first, rest)) = vec.split_first_chunk_mut::<2>() {
	///     *first = [3, 4];
	///     rest[0] = 5;
	/// }
	/// assert_eq!(vec, [3, 4, 5]);
	///
	/// assert_eq!(vec.split_first_chunk_mut::<4>(), None);
	/// ```
	pub fn split_first_chunk_mut<const SIZE: usize>(&mut self) -> Option<(&mut [T; SIZE], &mut [T])> {
		self.as_mut_slice().split_first_chunk_mut()
	}

	/// Returns a mutable reference to the last `SIZE` elements and the remaining slice of the
	/// vector, or `None` if it is empty.
	///
	/// If the vector holds a shared reference, its contents are cloned into a unique allocation. To
	/// return an error if the vector is shared, without allocating or cloning, use
	/// [`try_split_last_chunk_mut`] instead.
	///
	/// [`try_split_last_chunk_mut`]: Self::try_split_last_chunk_mut
	///
	/// # Panics
	///
	/// Panics if allocation fails, for example in an out-of-memory condition.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([0, 1, 2]);
	///
	/// if let Some((rest, last)) = vec.split_last_chunk_mut::<2>() {
	///     *last = [3, 4];
	///     rest[0] = 5;
	/// }
	/// assert_eq!(vec, [5, 3, 4]);
	///
	/// assert_eq!(vec.split_last_chunk_mut::<4>(), None);
	/// ```
	pub fn split_last_chunk_mut<const SIZE: usize>(&mut self) -> Option<(&mut [T], &mut [T; SIZE])> {
		self.as_mut_slice().split_last_chunk_mut()
	}

	/// Returns an element or subslice of the vector at an index, or `None` if the index is out of
	/// bounds.
	///
	/// If the vector holds a shared reference, its contents are cloned into a unique allocation. To
	/// return an error if the vector is shared, without allocating or cloning, use [`try_get_mut`]
	/// instead.
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
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([0, 1, 2]);
	///
	/// if let Some(elem) = vec.get_mut(1) {
	///     *elem = 42;
	/// }
	/// assert_eq!(vec, [0, 42, 2]);
	///
	/// assert_eq!(vec.get_mut(3), None);
	/// ```
	pub fn get_mut<I>(&mut self, index: I) -> Option<&mut I::Output>
	where
		I: SliceIndex<[T]>
	{
		self.as_mut_slice().get_mut(index)
	}

	/// Swaps two elements in the vector.
	///
	/// If the vector holds a shared reference, its contents are cloned into a unique allocation. To
	/// return an error if the vector is shared, without allocating or cloning, use [`try_swap`]
	/// instead.
	///
	/// [`try_swap`]: Self::try_swap
	///
	/// # Panics
	///
	/// Panics if:
	/// - allocation fails, for example in an out-of-memory condition
	/// - either index is out of bounds
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([1, 2, 3, 4, 5]);
	///
	/// vec.swap(1, 3);
	/// assert_eq!(vec, [1, 4, 3, 2, 5]);
	/// ```
	pub fn swap(&mut self, i: usize, j: usize) {
		self.as_mut_slice().swap(i, j);
	}

	/// Reverses the order of elements in the vector.
	///
	/// If the vector holds a shared reference, its contents are cloned into a unique allocation. To
	/// return an error if the vector is shared, without allocating or cloning, use [`try_reverse`]
	/// instead.
	///
	/// [`try_reverse`]: Self::try_reverse
	///
	/// # Panics
	///
	/// Panics if allocation fails, for example in an out-of-memory condition.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([1, 2, 3]);
	/// vec.reverse();
	/// assert_eq!(vec, [3, 2, 1]);
	/// ```
	pub fn reverse(&mut self) {
		self.as_mut_slice().reverse();
	}

	/// Returns an iterator that yields mutable references to each element.
	///
	/// If the vector holds a shared reference, its contents are cloned into a unique allocation. To
	/// return an error if the vector is shared, without allocating or cloning, use [`try_iter_mut`]
	/// instead.
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
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([1, 2, 4]);
	///
	/// for elem in vec.iter_mut() {
	///     *elem += 2;
	/// }
	/// assert_eq!(vec, [3, 4, 6]);
	/// ```
	pub fn iter_mut(&mut self) -> IterMut<T> {
		self.as_mut_slice().iter_mut()
	}

	/// Returns an iterator over `chunk_size` elements of the vector at a time, starting at the
	/// beginning of the vector.
	///
	/// The chunks are mutable slices, and do not overlap. If `chunk_size` does not divide the
	/// length of the vector, then the last chunk will not have length `chunk_size`.
	///
	/// See [`try_chunks_exact_mut`] for a variant of this iterator that returns chunks of exactly
	/// `chunk_size` elements, and [`try_rchunks_mut`] for the same iterator but starting at the end
	/// of the vector.
	///
	/// If the vector holds a shared reference, its contents are cloned into a unique allocation. To
	/// return an error if the vector is shared, without allocating or cloning, use
	/// [`try_chunks_mut`] instead.
	///
	/// [`try_chunks_exact_mut`]: Self::try_chunks_exact_mut
	/// [`try_rchunks_mut`]: Self::try_rchunks_mut
	/// [`try_chunks_mut`]: Self::try_chunks_mut
	///
	/// # Panics
	///
	/// Panics if:
	/// - allocation fails, for example in an out-of-memory condition
	/// - `chunk_size` is zero
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([0, 0, 0, 0, 0]);
	/// let mut count = 1;
	///
	/// for chunk in vec.chunks_mut(2) {
	///     chunk.fill(count);
	///     count += 1;
	/// }
	///
	/// assert_eq!(vec, [1, 1, 2, 2, 3]);
	/// ```
	pub fn chunks_mut(&mut self, chunk_size: usize) -> ChunksMut<T> {
		assert_ne!(chunk_size, 0, "chunk size must be non-zero");
		self.as_mut_slice().chunks_mut(chunk_size)
	}

	/// Returns an iterator over `chunk_size` elements of the vector at a time, starting at the
	/// beginning of the vector.
	///
	/// The chunks are mutable slices, and do not overlap. If `chunk_size` does not divide the
	/// length of the vector, then the last up to `chunk_size - 1` elements will be omitted and can
	/// be retrieved from the `into_remainder` function of the iterator.
	///
	/// Due to each chunk having exactly `chunk_size` elements, the compiler can often optimize the
	/// resulting code better than in the case of [`try_chunks_mut`].
	///
	/// See [`try_chunks_mut`] for a variant of this iterator that also returns the remainder as a
	/// smaller chunk, and [`try_rchunks_exact_mut`] for the same iterator but starting at the end
	/// of the vector.
	///
	/// If the vector holds a shared reference, its contents are cloned into a unique allocation. To
	/// return an error if the vector is shared, without allocating or cloning, use
	/// [`try_chunks_exact_mut`] instead.
	///
	/// [`try_chunks_mut`]: Self::try_chunks_mut
	/// [`try_rchunks_exact_mut`]: Self::try_rchunks_exact_mut
	/// [`try_chunks_exact_mut`]: Self::try_chunk_exact_mut
	///
	/// # Panics
	///
	/// Panics if:
	/// - allocation fails, for example in an out-of-memory condition
	/// - `chunk_size` is zero
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([0, 0, 0, 0, 0]);
	/// let mut count = 1;
	///
	/// for chunk in vec.chunks_exact_mut(2) {
	///     chunk.fill(count);
	///     count += 1;
	/// }
	///
	/// assert_eq!(vec, [1, 1, 2, 2, 0]);
	/// ```
	pub fn chunks_exact_mut(&mut self, chunk_size: usize) -> ChunksExactMut<T> {
		assert_ne!(chunk_size, 0, "chunk size must be non-zero");
		self.as_mut_slice().chunks_exact_mut(chunk_size)
	}

	/// Returns an iterator over `chunk_size` elements of the vector at a time, starting at the end
	/// of the vector.
	///
	/// The chunks are mutable slices, and do not overlap. If `chunk_size` does not divide the
	/// length of the vector, then the last chunk will not have length `chunk_size`.
	///
	/// See [`try_rchunks_exact_mut`] for a variant of this iterator that returns chunks of exactly
	/// `chunk_size` elements, and [`try_chunks_mut`] for the same iterator but starting at the
	/// beginning of the vector.
	///
	/// If the vector holds a shared reference, its contents are cloned into a unique allocation. To
	/// return an error if the vector is shared, without allocating or cloning, use
	/// [`try_rchunks_mut`] instead.
	///
	/// [`try_rchunks_exact_mut`]: Self::try_rchunks_exact_mut
	/// [`try_chunks_mut`]: Self::try_chunks_mut
	/// [`try_rchunks_mut`]: Self::try_rchunks_mut
	///
	/// # Panics
	///
	/// Panics if:
	/// - allocation fails, for example in an out-of-memory condition
	/// - `chunk_size` is zero
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([0, 0, 0, 0, 0]);
	/// let mut count = 1;
	///
	/// for chunk in vec.rchunks_mut(2) {
	///     chunk.fill(count);
	///     count += 1;
	/// }
	///
	/// assert_eq!(vec, [3, 2, 2, 1, 1]);
	/// ```
	pub fn rchunks_mut(&mut self, chunk_size: usize) -> RChunksMut<T> {
		assert_ne!(chunk_size, 0, "chunk size must be non-zero");
		self.as_mut_slice().rchunks_mut(chunk_size)
	}

	/// Returns an iterator over `chunk_size` elements of the vector at a time, starting at the end
	/// of the vector.
	///
	/// The chunks are mutable slices, and do not overlap. If `chunk_size` does not divide the
	/// length of the vector, then the last up to `chunk_size - 1` elements will be omitted and can
	/// be retrieved from the `into_remainder` function of the iterator.
	///
	/// Due to each chunk having exactly `chunk_size` elements, the compiler can often optimize the
	/// resulting code better than in the case of [`try_chunks_mut`].
	///
	/// See [`try_rchunks_mut`] for a variant of this iterator that also returns the remainder as a
	/// smaller chunk, and [`try_chunks_exact_mut`] for the same iterator but starting at the
	/// beginning of the vector.
	///
	/// If the vector holds a shared reference, its contents are cloned into a unique allocation. To
	/// return an error if the vector is shared, without allocating or cloning, use
	/// [`try_rchunks_exact_mut`] instead.
	///
	/// [`try_chunks_mut`]: Self::try_chunks_mut
	/// [`try_rchunks_mut`]: Self::try_rchunks_mut
	/// [`try_chunks_exact_mut`]: Self::try_chunks_exact_mut
	/// [`try_rchunks_exact_mut`]: Self::try_rchunks_exact_mut
	///
	/// # Panics
	///
	/// Panics if:
	/// - allocation fails, for example in an out-of-memory condition
	/// - `chunk_size` is zero
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([0, 0, 0, 0, 0]);
	/// let mut count = 1;
	///
	/// for chunk in vec.rchunks_exact_mut(2) {
	///     chunk.fill(count);
	///     count += 1;
	/// }
	///
	/// assert_eq!(vec, [0, 2, 2, 1, 1]);
	/// ```
	pub fn rchunks_exact_mut(&mut self, chunk_size: usize) -> RChunksExactMut<T> {
		assert_ne!(chunk_size, 0, "chunk size must be non-zero");
		self.as_mut_slice().rchunks_exact_mut(chunk_size)
	}

	// Todo: add `chunks_by_mut` and `rchunks_by_mut`, stabilized in 1.77?

	/// Divides the vector into two mutable slices at an index.
	///
	/// The first slice will contain all indices from `[0, mid)` (excluding the index `mid` itself)
	/// and the second will contain all indices from `[mid, len)` (excluding the index `len` itself).
	///
	/// If the vector holds a shared reference, its contents are cloned into a unique allocation. To
	/// return an error if the vector is shared, without allocating or cloning, use
	/// [`try_split_at_mut`] instead.
	///
	/// [`try_split_at_mut`]: Self::try_split_at_mut
	///
	/// # Panics
	///
	/// Panics if:
	/// - allocation fails, for example in an out-of-memory condition
	/// - `mid` is greater than `len`
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([1, 0, 3, 0, 5, 6]);
	///
	/// let (left, right) = vec.split_at_mut(2);
	/// assert_eq!(left, [1, 0]);
	/// assert_eq!(right, [3, 0, 5, 6]);
	/// left[1] = 2;
	/// right[1] = 4;
	///
	/// assert_eq!(vec, [1, 2, 3, 4, 5, 6]);
	/// ```
	pub fn split_at_mut(&mut self, mid: usize) -> (&mut [T], &mut [T]) {
		assert!(mid <= self.len(), "midpoint out of bounds");
		self.as_mut_slice().split_at_mut(mid)
	}

	// Todo: add `split_at_mut_checked`, stabilized in 1.80, and `split_at_mut_unchecked`, stabilized
	//  in 1.79

	/// Returns an iterator over mutable subslices separated by elements that match `pred`. The
	/// matched element is not contained in the subslices.
	///
	/// If the vector holds a shared reference, its contents are cloned into a unique allocation. To
	/// return an error if the vector is shared, without allocating or cloning, use [`try_split_mut`]
	/// instead.
	///
	/// [`try_split_mut`]: Self::try_split_mut
	///
	/// # Panics
	///
	/// Panics if allocation fails, for example in an out-of-memory condition.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([10, 40, 30, 20, 60, 50]);
	///
	/// for group in vec.split_mut(|&num| num % 3 == 0) {
	///     group[0] = 1;
	/// }
	///
	/// assert_eq!(vec, [1, 40, 30, 1, 60, 1]);
	/// ```
	pub fn split_mut<F>(&mut self, pred: F) -> SplitMut<T, F>
	where
		F: FnMut(&T) -> bool,
	{
		self.as_mut_slice().split_mut(pred)
	}

	/// Returns an iterator over mutable subslices separated by elements that match `pred`. The
	/// matched element is contained in the previous subslice as a terminator.
	///
	/// If the vector holds a shared reference, its contents are cloned into a unique allocation. To
	/// return an error if the vector is shared, without allocating or cloning, use
	/// [`try_split_inclusive_mut`] instead.
	///
	/// [`try_split_inclusive_mut`]: Self::try_split_inclusive_mut
	///
	/// # Panics
	///
	/// Panics if allocation fails, for example in an out-of-memory condition.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([10, 40, 30, 20, 60, 50]);
	///
	/// for group in vec.split_inclusive_mut(|&num| num % 3 == 0) {
	///     let terminator_idx = group.len() - 1;
	///     group[terminator_idx] = 1;
	/// }
	///
	/// assert_eq!(vec, [10, 40, 1, 20, 1, 1]);
	/// ```
	pub fn split_inclusive_mut<F>(&mut self, pred: F) -> SplitInclusiveMut<T, F>
	where
		F: FnMut(&T) -> bool,
	{
		self.as_mut_slice().split_inclusive_mut(pred)
	}

	/// Returns an iterator over mutable subslices separated by elements that match `pred`, starting
	/// at the end of the vector and working backwards. The matched element is not contained in the
	/// subslices.
	///
	/// If the vector holds a shared reference, its contents are cloned into a unique allocation. To
	/// return an error if the vector is shared, without allocating or cloning, use
	/// [`try_rsplit_mut`] instead.
	///
	/// [`try_rsplit_mut`]: Self::try_rsplit_mut
	///
	/// # Panics
	///
	/// Panics if allocation fails, for example in an out-of-memory condition.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([10, 40, 30, 20, 60, 50]);
	///
	/// for group in vec.rsplit_mut(|&num| num % 3 == 0) {
	///     group[0] = 1;
	/// }
	/// assert_eq!(vec, [1, 40, 30, 1, 60, 1]);
	/// ```
	pub fn rsplit_mut<F>(&mut self, pred: F) -> RSplitMut<T, F>
	where
		F: FnMut(&T) -> bool,
	{
		self.as_mut_slice().rsplit_mut(pred)
	}

	/// Returns an iterator over mutable subslices separated by elements that match `pred`, limited
	/// to returning at most `n` items. The matched element is not contained in the subslices.
	///
	/// The last element returned, if any, will contain the remainder of the vector.
	///
	/// If the vector holds a shared reference, its contents are cloned into a unique allocation. To
	/// return an error if the vector is shared, without allocating or cloning, use
	/// [`try_splitn_mut`] instead.
	///
	/// [`try_splitn_mut`]: Self::try_splitn_mut
	///
	/// # Panics
	///
	/// Panics if allocation fails, for example in an out-of-memory condition.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([10, 40, 30, 20, 60, 50]);
	///
	/// for group in vec.splitn_mut(2, |&num| num % 3 == 0) {
	///     group[0] = 1;
	/// }
	///
	/// assert_eq!(vec, [1, 40, 30, 1, 60, 50]);
	/// ```
	pub fn splitn_mut<F>(&mut self, n: usize, pred: F) -> SplitNMut<T, F>
	where
		F: FnMut(&T) -> bool,
	{
		self.as_mut_slice().splitn_mut(n, pred)
	}

	/// Returns an iterator over subslices separated by elements that match `pred` limited to
	/// returning at most `n` items. This starts at the end of the vector and works backwards. The
	/// matched element is not contained in the subslices.
	///
	/// The last element returned, if any, will contain the remainder of the vector.
	///
	/// If the vector holds a shared reference, its contents are cloned into a unique allocation. To
	/// return an error if the vector is shared, without allocating or cloning, use
	/// [`try_rsplitn_mut`] instead.
	///
	/// [`try_rsplitn_mut`]: Self::try_rsplitn_mut
	///
	/// # Panics
	///
	/// Panics if allocation fails, for example in an out-of-memory condition.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([10, 40, 30, 20, 60, 50]);
	///
	/// for group in vec.rsplitn_mut(2, |&num| num % 3 == 0) {
	///     group[0] = 1;
	/// }
	///
	/// assert_eq!(vec, [1, 40, 30, 20, 60, 1]);
	/// ```
	pub fn rsplitn_mut<F>(&mut self, n: usize, pred: F) -> RSplitNMut<T, F>
	where
		F: FnMut(&T) -> bool,
	{
		self.as_mut_slice().rsplitn_mut(n, pred)
	}

	// Todo: add `sort_unstable`, `select_nth_unstable`, etc., and `sort`, `sort_by`, etc. which
	//  allocate intermediate memory.

	/// Rotates the vector in-place such that the first `mid` elements of the vector move to the end
	/// while the last `len - mid` elements move to the start.
	///
	/// After calling `rotate_left`, the element previously at index `mid` will become the first
	/// element in the vector.
	///
	/// If the vector holds a shared reference, its contents are cloned into a unique allocation. To
	/// return an error if the vector is shared, without allocating or cloning, use
	/// [`try_rotate_left`] instead.
	///
	/// [`try_rotate_left`]: Self::try_rotate_left
	///
	/// # Panics
	///
	/// Panics if allocation fails, for example in an out-of-memory condition.
	///
	/// This function will panic if `mid` is greater than the length of the vector. Note that
	/// `mid == len` does _not_ panic and is a no-op rotation.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<char> = Vec::from(['a', 'b', 'c', 'd', 'e', 'f']);
	/// vec.rotate_left(2);
	/// assert_eq!(vec, ['c', 'd', 'e', 'f', 'a', 'b']);
	/// ```
	pub fn rotate_left(&mut self, mid: usize) {
		assert!(mid <= self.len(), "midpoint out of bounds");
		self.as_mut_slice().rotate_left(mid);
	}

	/// Rotates the vector in-place such that the first `len - k` elements of the vector move to the
	/// end while the last `k` elements move to the start.
	///
	/// After calling `rotate_right`, the element previously at index `len - k` will become the
	/// first element in the vector.
	///
	/// If the vector holds a shared reference, its contents are cloned into a unique allocation. To
	/// return an error if the vector is shared, without allocating or cloning, use
	/// [`try_rotate_right`] instead.
	///
	/// [`try_rotate_right`]: Self::try_rotate_right
	///
	/// # Panics
	///
	/// Panics if allocation fails, for example in an out-of-memory condition.
	///
	/// This function will panic if `k` is greater than the length of the vector. Note that
	/// `k == len` does _not_ panic and is a no-op rotation.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<char> = Vec::from(['a', 'b', 'c', 'd', 'e', 'f']);
	/// vec.rotate_right(2);
	/// assert_eq!(vec, ['e', 'f', 'a', 'b', 'c', 'd']);
	/// ```
	pub fn rotate_right(&mut self, k: usize) {
		assert!(k <= self.len(), "midpoint out of bounds");
		self.as_mut_slice().rotate_right(k);
	}

	/// Fills the current vector length by cloning `value`.
	///
	/// If the vector holds a shared reference, its contents are cloned into a unique allocation. To
	/// return an error if the vector is shared, without allocating or cloning, use [`try_fill`]
	/// instead.
	///
	/// [`try_fill`]: Self::try_fill
	///
	/// # Panics
	///
	/// Panics if allocation fails, for example in an out-of-memory condition.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([0; 8]);
	/// vec.fill(1);
	/// assert_eq!(vec, [1; 8]);
	/// ```
	pub fn fill(&mut self, value: T) {
		if let Ok(slice) = self.try_as_mut_slice() {
			slice.fill(value);
			return
		}
		// Todo: if not empty, avoid cloning elements from the original vector by creating a new
		//  vector and calling `extend`. Avoid corruption on panic by tracking how many elements
		//  have been filled, and filling the rest by cloning from the original on panic.
	}

	/// Fills the current vector length with elements returned by calling a closure repeatedly.
	///
	/// This method uses a closure to create new values. If you'd rather [`Clone`] a given value,
	/// use [`try_fill`]. If you want to use the [`Default`] trait to generate values, you can pass
	/// [`Default::default`] as the argument.
	///
	/// If the vector holds a shared reference, its contents are cloned into a unique allocation. To
	/// return an error if the vector is shared, without allocating or cloning, use
	/// [`try_fill_with`] instead.
	///
	/// [`try_fill`]: Self::try_fill
	/// [`try_fill_with`]: Self::try_fill_with
	///
	/// # Panics
	///
	/// Panics if allocation fails, for example in an out-of-memory condition.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::vec::rc::Vec;
	///
	/// let mut vec: Vec<i32> = Vec::from([1; 8]);
	/// vec.fill_with(Default::default);
	/// assert_eq!(vec, [0; 10]);
	/// ```
	pub fn fill_with<F>(&mut self, mut fill: F)
	where
		F: FnMut() -> T,
	{
		if let Ok(slice) = self.try_as_mut_slice() {
			for elem in slice {
				*elem = fill();
			}

			return
		}
		// Todo: if not empty, avoid cloning by creating a new vector and calling `extend`. Avoid
		//  corruption on panic by tracking how many elements have been filled, and filling the rest
		//  by cloning from the original on panic.
	}
}

impl<T, A: Allocator, const ATOMIC: bool> Deref for Vec<T, ATOMIC, A> {
	type Target = [T];

	fn deref(&self) -> &[T] {
		self.as_slice()
	}
}

impl<T, A: Allocator + Clone, const ATOMIC: bool> Clone for Vec<T, ATOMIC, A> {
	/// Creates a new vector sharing its contents with this vector.
	fn clone(&self) -> Self {
		todo!()
	}
}

impl<T: Hash, A: Allocator, const ATOMIC: bool> Hash for Vec<T, ATOMIC, A> {
	fn hash<H: Hasher>(&self, state: &mut H) {
		Hash::hash(&**self, state)
	}
}

impl<T, I: SliceIndex<[T]>, A: Allocator, const ATOMIC: bool> Index<I> for Vec<T, ATOMIC, A> {
	type Output = I::Output;

	fn index(&self, index: I) -> &Self::Output {
		Index::index(&**self, index)
	}
}

impl<T, const ATOMIC: bool> FromIterator<T> for Vec<T, ATOMIC> {
	fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
		todo!()
	}
}

impl<T: Clone, A: Allocator, const ATOMIC: bool> IntoIterator for Vec<T, ATOMIC, A> {
	type Item = T;
	type IntoIter = IntoIter<T, A, ATOMIC>;

	/// Consumes the vector into an iterator yielding elements by value. If the vector is shared,
	/// the elements are cloned out of the vector.
	fn into_iter(self) -> Self::IntoIter {
		todo!()
	}
}

impl<'a, T, A: Allocator, const ATOMIC: bool> IntoIterator for &'a Vec<T, ATOMIC, A> {
	type Item = &'a T;
	type IntoIter = Iter<'a, T>;

	fn into_iter(self) -> Self::IntoIter {
		self.as_slice().iter()
	}
}

impl<'a, T: Clone, A: Allocator + Clone, const ATOMIC: bool> IntoIterator for &'a mut Vec<T, ATOMIC, A> {
	type Item = &'a mut T;
	type IntoIter = IterMut<'a, T>;

	/// # Panics
	///
	/// Panics if allocation fails, for example in an out-of-memory condition.
	fn into_iter(self) -> Self::IntoIter {
		self.as_mut_slice().iter_mut()
	}
}

impl<T: Clone, A: Allocator + Clone, const ATOMIC: bool> Extend<T> for Vec<T, ATOMIC, A> {
	fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
		todo!()
	}

	#[cfg(feature = "unstable-traits")]
	fn extend_one(&mut self, item: T) {
		todo!()
	}

	#[cfg(feature = "unstable-traits")]
	fn extend_reserve(&mut self, additional: usize) {
		todo!()
	}
}

impl<'a, T: Copy + 'a, A: Allocator + Clone, const ATOMIC: bool> Extend<&'a T> for Vec<T, ATOMIC, A> {
	fn extend<I: IntoIterator<Item = &'a T>>(&mut self, iter: I) {
		todo!()
	}

	#[cfg(feature = "unstable-traits")]
	fn extend_one(&mut self, item: &'a T) {
		todo!()
	}

	#[cfg(feature = "unstable-traits")]
	fn extend_reserve(&mut self, additional: usize) {
		todo!()
	}
}

impl<T: Eq, A: Allocator, const ATOMIC: bool> Eq for Vec<T, ATOMIC, A> { }

impl<T, A1, A2, const ATOMIC1: bool, const ATOMIC2: bool> PartialOrd<Vec<T, ATOMIC2, A2>> for Vec<T, ATOMIC1, A1>
where
	T: PartialOrd,
	A1: Allocator,
	A2: Allocator
{
	fn partial_cmp(&self, other: &Vec<T, ATOMIC2, A2>) -> Option<Ordering> {
		PartialOrd::partial_cmp(&**self, &**other)
	}
}

impl<T: Ord, A: Allocator, const ATOMIC: bool> Ord for Vec<T, ATOMIC, A> {
	fn cmp(&self, other: &Self) -> Ordering {
		Ord::cmp(&**self, &**other)
	}
}

impl<T, A: Allocator, const ATOMIC: bool> Drop for Vec<T, ATOMIC, A> {
	fn drop(&mut self) {
		todo!()
	}
}

impl<T, const ATOMIC: bool> Default for Vec<T, ATOMIC> {
	fn default() -> Self {
		Self::new()
	}
}

impl<T: fmt::Debug, A: Allocator, const ATOMIC: bool> fmt::Debug for Vec<T, ATOMIC, A> {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		fmt::Debug::fmt(&**self, f)
	}
}

impl<T, A: Allocator, const ATOMIC: bool> AsRef<Self> for Vec<T, ATOMIC, A> {
	fn as_ref(&self) -> &Self {
		self
	}
}

impl<T, A: Allocator, const ATOMIC: bool> AsMut<Self> for Vec<T, ATOMIC, A> {
	fn as_mut(&mut self) -> &mut Self {
		self
	}
}

impl<T, A: Allocator, const ATOMIC: bool> AsRef<[T]> for Vec<T, ATOMIC, A> {
	fn as_ref(&self) -> &[T] {
		self
	}
}

// Array and slice conversions

impl<T: Clone, const N: usize, const ATOMIC: bool> From<&[T; N]> for Vec<T, ATOMIC> {
	fn from(value: &[T; N]) -> Self {
		todo!()
	}
}

impl<T: Clone, const N: usize, const ATOMIC: bool> From<&mut [T; N]> for Vec<T, ATOMIC> {
	fn from(value: &mut [T; N]) -> Self {
		todo!()
	}
}

impl<T, const ATOMIC: bool, const N: usize> From<[T; N]> for Vec<T, ATOMIC> {
	fn from(value: [T; N]) -> Self {
		todo!()
	}
}

impl<T: Clone, const N: usize, A: Allocator, const ATOMIC: bool> TryFrom<Vec<T, ATOMIC, A>> for [T; N] {
	type Error = Vec<T, ATOMIC, A>;

	/// Converts a [`Vec`] into an array, cloning out of a shared allocation.
	///
	/// # Errors
	///
	/// Returns the vector back in its length is too large or small to fit in the array size.
	fn try_from(value: Vec<T, ATOMIC, A>) -> Result<Self, Self::Error> {
		todo!()
	}
}

impl<T: Clone, const ATOMIC: bool> From<&[T]> for Vec<T, ATOMIC> {
	fn from(value: &[T]) -> Vec<T, ATOMIC> {
		todo!()
	}
}

impl<T: Clone, const ATOMIC: bool> From<&mut [T]> for Vec<T, ATOMIC> {
	fn from(value: &mut [T]) -> Vec<T, ATOMIC> {
		todo!()
	}
}

impl<const ATOMIC: bool> From<&str> for Vec<u8, ATOMIC> {
	fn from(value: &str) -> Vec<u8, ATOMIC> {
		value.as_bytes().into()
	}
}

// Fallible Box/Vec conversions

impl<T, A: Allocator, const ATOMIC: bool> From<StdVec<T, A>> for Vec<T, ATOMIC, A> {
	fn from(value: StdVec<T, A>) -> Self {
		todo!()
	}
}

impl<const ATOMIC: bool> From<String> for Vec<u8, ATOMIC> {
	fn from(value: String) -> Self {
		value.into_bytes().into()
	}
}

impl<T, A: Allocator, const ATOMIC: bool> From<Box<[T], A>> for Vec<T, ATOMIC, A> {
	fn from(value: Box<[T], A>) -> Self {
		todo!()
	}
}

impl<T, A: Allocator, const N: usize, const ATOMIC: bool> From<Box<[T; N], A>> for Vec<T, ATOMIC, A> {
	fn from(value: Box<[T; N], A>) -> Self {
		todo!()
	}
}

impl<A: Allocator, const ATOMIC: bool> From<Box<str, A>> for Vec<u8, ATOMIC, A> {
	fn from(value: Box<str, A>) -> Self {
		Box::<[u8], A>::from(value).into()
	}
}
