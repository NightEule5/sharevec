// Copyright 2025 - Strixpyrr
// SPDX-License-Identifier: Apache-2.0

use core::alloc::Allocator;
use core::cmp::Ordering;
use core::fmt;
use core::hash::{Hash, Hasher};
use core::marker::PhantomData;
use core::ops::{Index, IndexMut, RangeBounds};
use core::ptr::NonNull;
use crate::error::Result;
use crate::macros::*;
use crate::marker::UniqueVector;
use super::{Deque, Drain, Iter, IterMut};

/// A mutable view over an [`Deque`] with a unique reference, obtained by [`Deque::unique`] or
/// [`Deque::as_unique`].
///
/// This type provides a compile-time guarantee that the deque holds a unique reference[^weak] for
/// the lifetime of the borrow. Once this wrapper is dropped, modifying the deque may fail. This is
/// possible because the compiler does not allow multiple references to a mutably-referenced value.
/// To clone the deque and make it immutable, it must be borrowed, which the compiler does not
/// allow while this type holds its mutable reference.
///
/// [^weak]: for the purposes of this guarantee, no weak references are allowed. This is because a
/// weak reference could be upgraded to a strong reference while this wrapper still exists, enabling
/// mutability on a shared deque.
pub struct Unique<'a, T: 'a, A: Allocator + 'a, const ATOMIC: bool> {
	_ref: PhantomData<&'a mut Deque<T, ATOMIC, A>>,
}

impl<T, A: Allocator, const ATOMIC: bool> Unique<'_, T, A, ATOMIC> {
	/// Consumes the reference, returning a deque with a shared reference.
	pub fn into_shared(self) -> Deque<T, ATOMIC, A> where A: Clone {
		delegate!(self.clone())
	}

	/// Returns the total number of elements the deque can hold.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::{Deque, Unique};
	///
	/// let mut deque = Deque::with_capacity(8);
	/// let unique: Unique<i32> = deque.as_unique();
	/// assert!(unique.capacity() >= 8);
	/// ```
	pub const fn capacity(&self) -> usize {
		delegate!(self.capacity())
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
	/// let mut deque = Deque::with_capacity(5);
	/// let mut unique = deque.as_unique();
	/// unique.push_back(0);
	/// unique.push_back(1);
	/// unique.push_back(2);
	///
	/// assert_eq!(unique.as_slices(), (&[0, 1, 2][..], &[][..]));
	///
	/// unique.push_front(10);
	/// unique.push_front(9);
	///
	/// assert_eq!(unique.as_slices(), (&[9, 10][..], &[0, 1, 2][..]));
	/// ```
	pub fn as_slices(&self) -> (&[T], &[T]) {
		delegate!(self.as_slices())
	}

	/// Returns a pair of mutable slices over the contents of the deque.
	///
	/// If the deque is contiguous, all elements will be in the first slice and the second will be
	/// empty.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::{Deque, Unique};
	///
	/// let mut deque = Deque::with_capacity(4);
	/// let mut unique: Unique<i32> = deque.as_unique();
	/// unique.push_back(0);
	/// unique.push_back(1);
	///
	/// unique.push_front(10);
	/// unique.push_front(9);
	///
	/// unique.as_mut_slices().0[0] = 42;
	/// unique.as_mut_slices().1[0] = 24;
	///
	/// assert_eq!(unique.as_slices(), (&[42, 10][..], &[24, 1][..]));
	/// ```
	pub fn as_mut_slices(&mut self) -> (&mut [T], &mut [T]) {
		delegate!(self.try_as_mut_slices() -> shared)
	}

	/// Returns a raw pointer to the deque's buffer.
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
	/// This pointer remains valid even when the [`Unique`] wrapper goes out of scope, as long as
	/// the referenced deque remains in scope.
	///
	/// [`as_mut_ptr`]: Self::as_mut_ptr
	/// [`as_ptr`]: Self::as_ptr
	/// [`as_non_null`]: Self::as_non_null
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::{Deque, Unique};
	///
	/// let mut deque = Deque::from([1, 2, 4]);
	/// let mut unique: Unique<i32> = deque.as_unique();
	/// let ptr = unique.as_ptr();
	///
	/// unsafe {
	///     for i in 0..unique.len() {
	///         assert_eq!(*ptr.add(i), 1 << i);
	///     }
	/// }
	/// ```
	///
	/// Due to the aliasing guarantee, this code is valid:
	///
	/// ```
	/// use sharevec::deque::rc::{Deque, Unique};
	///
	/// let mut deque = Deque::from([1, 2, 3]);
	/// let mut unique: Unique<i32> = deque.as_unique();
	/// unsafe {
	///     let ptr1 = unique.as_ptr();
	///     assert_eq!(ptr1.read(), 1);
	///     let ptr2 = unique.as_mut_ptr().offset(2);
	///     ptr2.write(2);
	///     // Notably, writing to `ptr2` did *not* invalidate `ptr1`
	///     // because it mutated a different element:
	///     _ = ptr1.read();
	/// }
	/// ```
	pub fn as_ptr(&self) -> *const T {
		delegate!(self.as_ptr())
	}
	/// Returns a raw pointer to the deque's buffer.
	///
	/// The caller must ensure that the deque outlives the pointer this function returns, or else
	/// it will end up dangling. Modifying the deque may cause its buffer to be reallocated, which
	/// would also make any pointers to it invalid.
	///
	/// This method guarantees that for the purpose of the aliasing model, this method does not
	/// materialize a reference to the underlying slice, and thus the returned pointer will remain
	/// valid when mixed with other calls to [`as_ptr`], [`as_mut_ptr`], and [`as_non_null`]. Note
	/// that calling other methods that materialize mutable references to the slice, or mutable
	/// references to specific elements you are planning on accessing through this pointer, as well
	/// as writing to those elements, may still invalidate this pointer.
	///
	/// This pointer remains valid even when the [`Unique`] wrapper goes out of scope, as long as
	/// the referenced deque remains in scope. Once this wrapper is dropped, the same mutability
	/// rules as [`Deque::as_mut_ptr`] apply.
	///
	/// [`as_mut_ptr`]: Self::as_mut_ptr
	/// [`as_ptr`]: Self::as_ptr
	/// [`as_non_null`]: Self::as_non_null
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::{Deque, Unique};
	///
	/// let mut deque = Deque::from([0; 8]);
	/// let mut unique: Unique<i32> = deque.as_unique();
	/// let ptr = unique.as_mut_ptr();
	///
	/// // Initialize elements via raw pointer writes.
	/// // This is safe because no other strong reference points to the vector contents.
	/// unsafe {
	///     for i in 0..unique.len() {
	///         ptr.add(i).write(i as i32);
	///     }
	/// }
	/// assert_eq!(unique, [1, 2, 3, 4, 5, 6, 7, 8]);
	/// ```
	///
	/// Due to the aliasing guarantee, this code is valid:
	///
	/// ```
	/// use sharevec::deque::rc::{Deque, Unique};
	///
	/// let mut deque = Deque::from([0]);
	/// let mut deque: Unique<i32> = deque.as_unique();
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
		delegate!(mut self.as_mut_ptr())
	}
	/// Returns a `NonNull` pointer to the deque's buffer.
	///
	/// The caller must ensure that the deque outlives the pointer this function returns, or else
	/// will end up dangling. Modifying the deque may cause its buffer to be reallocated, which
	/// would also make any pointers to it invalid.
	///
	/// This method guarantees that for the purpose of the aliasing model, this method does not
	/// materialize a reference to the underlying slice, and thus the returned pointer will remain
	/// valid when mixed with other calls to [`as_ptr`], [`as_mut_ptr`], and [`as_non_null`]. Note
	/// that calling other methods that materialize mutable references to the slice, or mutable
	/// references to specific elements you are planning on accessing through this pointer, as well
	/// as writing to those elements, may still invalidate this pointer.
	///
	/// This pointer remains valid even when the [`Unique`] wrapper goes out of scope, as long as
	/// the referenced deque remains in scope. Once this wrapper is dropped, the same mutability
	/// rules as [`Deque::as_mut_ptr`] apply.
	///
	/// [`as_mut_ptr`]: Self::as_mut_ptr
	/// [`as_ptr`]: Self::as_ptr
	/// [`as_non_null`]: Self::as_non_null
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::{Deque, Unique};
	///
	/// let mut deque = Deque::from([0; 8]);
	/// let mut unique: Unique<i32> = deque.as_unique();
	/// let ptr = unique.as_non_null();
	///
	/// // Initialize elements via raw pointer writes.
	/// // This is safe because no other strong reference points to the vector contents.
	/// unsafe {
	///     for i in 0..unique.len() {
	///         ptr.add(i).write(i as i32);
	///     }
	/// }
	/// assert_eq!(unique, [1, 2, 3, 4, 5, 6, 7, 8]);
	/// ```
	///
	/// Due to the aliasing guarantee, this code is valid:
	///
	/// ```
	/// use sharevec::deque::rc::{Deque, Unique};
	///
	/// let mut deque = Deque::from([0]);
	/// let mut unique: Unique<i32> = deque.as_unique();
	/// unsafe {
	///     let ptr1 = unique.as_non_null();
	///     ptr1.write(1);
	///     let ptr2 = unique.as_non_null();
	///     ptr2.write(2);
	///     // Notably, writing to `ptr2` did *not* invalidate `ptr1`:
	///     ptr1.write(3);
	/// }
	/// ```
	pub fn as_non_null(&mut self) -> NonNull<T> {
		delegate!(mut self.as_non_null())
	}

	/// Returns a reference to the underlying allocator.
	pub fn allocator(&self) -> &A {
		delegate!(self.allocator())
	}

	/// Reserves space for at least `additional` elements. The deque may reserve more space to
	/// speculatively avoid frequent reallocations. The reserved capacity will be greater than or
	/// equal to `length + additional`. No memory is allocated if the capacity is already sufficient.
	///
	/// # Panics
	///
	/// Panics if the new capacity is greater than [`isize::MAX`] *bytes* minus four [`usize`]
	/// words.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::{Deque, Unique};
	///
	/// let mut deque = Deque::from([1]);
	/// let mut unique: Unique<i32> = deque.as_unique();
	/// unique.reserve(10);
	/// assert!(unique.capacity() >= 11);
	/// ```
	pub fn reserve(&mut self, additional: usize) {
		delegate!(self.try_reserve(additional) -> shared);
	}

	/// Reserves the minimum space for at least `additional` elements, without speculative
	/// over-allocation [`reserve`] does. The reserved will be greater than or equal to
	/// `length + additional`. No memory is allocated if the capacity is already sufficient.
	///
	/// The allocator may give the vector more space than it requests. Therefore, capacity cannot be
	/// relied upon to be precisely minimal. [`reserve`] is preferred if future insertions are
	/// expected.
	///
	/// [`reserve`]: Self::reserve
	///
	/// # Panics
	///
	/// Panics if the new capacity is greater than [`isize::MAX`] *bytes* minus four [`usize`]
	/// words.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::{Deque, Unique};
	///
	/// let mut deque = Deque::from([1]);
	/// let mut unique: Unique<i32> = deque.as_unique();
	/// unique.reserve_exact(10);
	/// assert!(unique.capacity() >= 11);
	/// ```
	pub fn reserve_exact(&mut self, additional: usize) {
		delegate!(self.try_reserve_exact(additional) -> shared);
	}

	// Todo: try_reserve with errors instead of panics, similar to VecDeque::try_reserve?

	/// Shrinks the capacity of the deque as much as possible.
	///
	/// The behavior of this method depends on the allocator, which may either shrink the deque
	/// in-place or reallocate. The resulting deque might still have some excess capacity, just as
	/// is the case for [`with_capacity`]. See [`Allocator::shrink`] for more details.
	///
	/// [`with_capacity`]: Self::with_capacity
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::{Deque, Unique};
	///
	/// let mut deque = Deque::with_capacity(10);
	/// let mut unique: Unique<i32> = deque.as_unique();
	/// unique.extend([1, 2, 3]);
	/// assert!(unique.capacity() >= 10);
	/// unique.shrink_to_fit();
	/// assert!(unique.capacity() >= 3);
	/// ```
	pub fn shrink_to_fit(&mut self) {
		delegate!(self.try_shrink_to_fit() -> shared);
	}

	/// Shrinks the capacity of the deque with a lower bound.
	///
	/// The capacity will be at least as large as both the length and the supplied value. If the
	/// current capacity is less than the lower limit, this does nothing.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::{Deque, Unique};
	///
	/// let mut deque = Deque::with_capacity(10);
	/// let mut unique: Unique<i32> = deque.as_unique();
	/// unique.extend([1, 2, 3]);
	/// assert!(unique.capacity() >= 10);
	/// unique.shrink_to(4);
	/// assert!(unique.capacity() >= 4);
	/// unique.shrink_to(0);
	/// assert!(unique.capacity() >= 3);
	/// ```
	pub fn shrink_to(&mut self, min_capacity: usize) {
		delegate!(self.try_shrink_to(min_capacity) -> shared);
	}

	/// Returns the number of elements in the deque.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque = Deque::from([1, 2, 3]);
	/// let unique = deque.as_unique();
	/// assert_eq!(unique.len(), 3);
	/// ```
	pub fn len(&self) -> usize {
		delegate!(self.len())
	}
	/// Returns `true` if the deque contains no elements.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::{Deque, Unique};
	///
	/// let mut deque = Deque::new();
	/// let mut unique: Unique<i32> = deque.as_unique();
	/// assert!(!unique.is_not_empty());
	///
	/// unique.push_back(1);
	/// assert!(unique.is_not_empty());
	/// ```
	pub fn is_empty(&self) -> bool {
		delegate!(self.is_empty())
	}
	/// Returns `true` if the deque contains any elements.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::{Deque, Unique};
	///
	/// let mut deque = Deque::new();
	/// let mut unique: Unique<i32> = deque.as_unique();
	/// assert!(!unique.is_not_empty());
	///
	/// unique.push_back(1);
	/// assert!(unique.is_not_empty());
	/// ```
	pub fn is_not_empty(&self) -> bool {
		delegate!(self.is_not_empty())
	}

	/// Returns a reference to the element at `index`, or `None` if the index is out of bounds.
	/// Index `0` is the front of the queue.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque = Deque::from([1, 2, 3]);
	/// let unique = deque.as_unique();
	/// assert_eq!(unique.get(1), Some(&2));
	/// assert_eq!(unique.get(3), None);
	/// ```
	pub fn get(&self, index: usize) -> Option<&T> {
		delegate!(self.get(index))
	}
	/// Returns a reference to the front element, or `None` if the deque is empty.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque = Deque::from([1, 2, 3]);
	/// let mut unique = deque.as_unique();
	/// assert_eq!(unique.front(), Some(&1));
	/// unique.clear();
	/// assert_eq!(unique.front(), None);
	/// ```
	pub fn front(&self) -> Option<&T> {
		delegate!(self.front())
	}
	/// Returns a reference to the back element, or `None` if the deque is empty.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque = Deque::from([1, 2, 3]);
	/// let mut unique = deque.as_unique();
	/// assert_eq!(unique.back(), Some(&3));
	/// unique.clear();
	/// assert_eq!(unique.back(), None);
	/// ```
	pub fn back(&self) -> Option<&T> {
		delegate!(self.back())
	}
	/// Returns a mutable reference to the element at `index`, or `None` if the index is out of
	/// bounds. Index `0` is the front of the queue.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque = Deque::from([1, 2, 3]);
	/// let mut unique = deque.as_unique();
	///
	/// if let Some(v) = unique.get_mut(1) {
	///     *v = 4;
	/// }
	/// assert_eq!(unique, [1, 4, 3]);
	/// ```
	pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
		delegate!(self.try_get_mut(index) -> shared)
	}
	/// Returns a mutable reference to the front element, or `None` if the deque is empty.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque = Deque::from([1, 2, 3]);
	/// let mut unique = deque.as_unique();
	///
	/// if let Some(v) = unique.front_mut() {
	///     *v = 4;
	/// }
	/// assert_eq!(unique, [4, 2, 3]);
	/// ```
	pub fn front_mut(&mut self) -> Option<&mut T> {
		delegate!(self.try_front_mut() -> shared)
	}
	/// Returns a mutable reference to the back element, or `None` if the deque is empty.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque = Deque::from([1, 2, 3]);
	/// let mut unique = deque.as_unique();
	///
	/// if let Some(v) = unique.back_mut() {
	///     *v = 4;
	/// }
	/// assert_eq!(unique, [1, 2, 4]);
	/// ```
	pub fn back_mut(&mut self) -> Option<&mut T> {
		delegate!(self.try_back_mut() -> shared)
	}
	/// Returns `true` if the deque contains an element equal to the given value.
	///
	/// This operation is *O*(*n*).
	///
	/// Note if that the deque is sorted, [`binary_search`] may be faster.
	///
	/// [`binary_search`]: Self::binary_search
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque = Deque::new();
	/// let mut unique = deque.as_unique();
	///
	/// unique.push_back(0);
	/// unique.push_back(1);
	///
	/// assert!(unique.contains(&1));
	/// assert!(!unique.contains(&10));
	/// ```
	pub fn contains(&self, value: &T) -> bool
	where
		T: PartialEq,
	{
		delegate!(self.contains(value))
	}

	/// Shortens the deque, keeping the first `len` elements and dropping the rest. If `len` is
	/// greater or equal to the deque's current length, this has no effect.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque = Deque::from([1, 2, 3, 4, 5]);
	/// let mut unique = deque.as_unique();
	/// // Truncates from 5 elements to 2
	/// unique.truncate(2);
	/// assert_eq!(unique, [1, 2]);
	/// // No truncation occurs when the length is greater than the deque's current length
	/// unique.truncate(8);
	/// assert_eq!(unique, [1, 2]);
	/// // Truncating to 0 elements is equivalent to `clear`
	/// unique.truncate(0);
	/// assert_eq!(unique, []);
	/// ```
	pub fn truncate(&mut self, len: usize) {
		delegate!(mut self.truncate(len));
	}

	/// Returns an iterator returning references to elements front-to-back.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque = Deque::from([1, 2, 3]);
	/// let unique = deque.as_unique();
	///
	/// assert!(unique.iter().eq(&[1, 2, 3]))
	/// ```
	pub fn iter(&self) -> Iter<T> {
		delegate!(self.iter())
	}
	/// Returns an iterator returning mutable references to elements front-to-back.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque = Deque::from([1, 2, 3]);
	/// let mut unique = deque.as_unique();
	///
	/// for v in unique.iter_mut() {
	///     *v *= 2;
	/// }
	///
	/// assert_eq!(unique, [2, 4, 6]);
	/// ```
	pub fn iter_mut(&mut self) -> IterMut<T> {
		delegate!(self.try_iter_mut() -> shared)
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
	/// let mut deque = Deque::from([1, 2, 3]);
	/// let mut unique = deque.as_unique();
	///
	/// let range = unique.range(2..);
	/// assert!(range.eq(&[3]));
	/// ```
	pub fn range<R: RangeBounds<usize>>(&self, range: R) -> Iter<T> {
		delegate!(self.range(range))
	}
	/// Returns an iterator returning mutable references to elements within a range.
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
	/// let mut deque = Deque::from([1, 2, 3]);
	/// let mut unique = deque.as_unique();
	/// for v in unique.range_mut(2..) {
	///     *v *= 2;
	/// }
	/// assert_eq!(unique, [1, 2, 6]);
	/// ```
	pub fn range_mut<R: RangeBounds<usize>>(&mut self, range: R) -> IterMut<T> {
		delegate!(self.try_range_mut(range) -> shared)
	}

	/// Removes the first element and returns it, or `None` if the deque is empty.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque = Deque::from([1, 2]);
	/// let mut unique = deque.as_unique();
	/// assert_eq!(unique.pop_front(), Some(1));
	/// assert_eq!(unique.pop_front(), Some(2));
	/// assert_eq!(unique.pop_front(), None);
	/// ```
	pub fn pop_front(&mut self) -> Option<T> {
		delegate!(self.try_pop_front() -> shared)
	}
	/// Removes the last element and returns it, or `None` if the deque is empty.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque = Deque::from([1, 2]);
	/// let mut unique = deque.as_unique();
	/// assert_eq!(unique.pop_back(), Some(2));
	/// assert_eq!(unique.pop_back(), Some(1));
	/// assert_eq!(unique.pop_back(), None);
	/// ```
	pub fn pop_back(&mut self) -> Option<T> {
		delegate!(self.try_pop_back() -> shared)
	}
	/// Prepends an element to the deque.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque = Deque::new();
	/// let mut unique = deque.as_unique();
	/// unique.push_front(1);
	/// unique.push_front(2);
	/// assert_eq!(unique, [2, 1]);
	/// ```
	pub fn push_front(&mut self, value: T) {
		delegate!(self.try_push_front(value) -> shared);
	}
	/// Appends an element to the back of the deque.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque = Deque::new();
	/// let mut unique = deque.as_unique();
	/// unique.push_back(1);
	/// unique.push_back(2);
	/// assert_eq!(unique, [1, 2]);
	/// ```
	pub fn push_back(&mut self, value: T) {
		delegate!(self.try_push_back(value) -> shared);
	}

	/// Swaps elements at indices `i` and `j`, where index `0` is the front of the queue. Both may
	/// be equal.
	///
	/// # Panics
	///
	/// Panics if either index is out of bounds.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque = Deque::from([1, 2, 3]);
	/// let mut unique = deque.as_unique();
	/// assert_eq!(unique, [1, 2, 3]);
	/// unique.swap(0, 2);
	/// assert_eq!(unique, [3, 2, 1]);
	/// ```
	pub fn swap(&mut self, i: usize, j: usize) {
		delegate!(self.try_swap(i, j) -> shared);
	}

	/// Removes and returns the element at `index` from the deque, replacing it with the first
	/// element. Index `0` is at the front of the queue.
	///
	/// This does not preserve ordering, but is *O*(1). If ordering must be preserved, use
	/// [`remove`].
	///
	/// Returns `None` if `index` is out of bounds.
	///
	/// [`remove`]: Self::remove
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque = Deque::from([1, 2, 3]);
	/// let mut unique = deque.as_unique();
	/// assert_eq!(unique.swap_remove_front(2), Some(3));
	/// assert_eq!(unique, [2, 1]);
	/// unique.clear();
	/// assert_eq!(unique.swap_remove_front(0), None);
	/// ```
	pub fn swap_remove_front(&mut self, index: usize) -> Option<T> {
		delegate!(self.try_swap_remove_front(index) -> shared)
	}
	/// Removes and returns the element at `index` from the deque, replacing it with the last
	/// element. Index `0` is at the front of the queue.
	///
	/// This does not preserve ordering, but is *O*(1). If ordering must be preserved, use
	/// [`remove`].
	///
	/// Returns `None` if `index` is out of bounds.
	///
	/// [`remove`]: Self::remove
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque = Deque::from([1, 2, 3]);
	/// let mut unique = deque.as_unique();
	/// assert_eq!(unique.swap_remove_back(0), Some(1));
	/// assert_eq!(unique, [3, 2]);
	/// unique.clear();
	/// assert_eq!(unique.swap_remove_back(0), None);
	/// ```
	pub fn swap_remove_back(&mut self, index: usize) -> Option<T> {
		delegate!(self.try_swap_remove_back(index) -> shared)
	}

	/// Removes and returns the element at `index` from the deque, shifting subsequent elements at
	/// whichever end is closer to the removal point. Index `0` is at the front of the queue.
	///
	/// Returns `None` if `index` is out of bounds.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque = Deque::from([1, 2, 3]);
	/// let mut unique = deque.as_unique();
	/// assert_eq!(unique.remove(1), Some(2));
	/// assert_eq!(unique, [1, 3]);
	/// ```
	pub fn remove(&mut self, index: usize) -> Option<T> {
		delegate!(self.try_remove(index) -> shared)
	}

	/// Inserts an element at position `index` within the deque, shifting subsequent elements toward
	/// the back. Index `0` is at the front of the queue.
	///
	/// # Errors
	///
	/// Returns the element back as an error if the deque is fill.
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
	/// let mut unique = deque.as_unique();
	/// unique.push_back(1);
	/// unique.push_back(3);
	/// unique.push_back(4);
	/// assert_eq!(unique, [1, 3, 4]);
	///
	/// unique.insert(1, 2);
	/// assert_eq!(unique, [1, 2, 3, 4]);
	/// ```
	pub fn insert(&mut self, index: usize, element: T) {
		delegate!(self.try_insert(index, element) -> shared);
	}

	/// Retains the elements specified by `predicate`, dropping the rest.
	///
	/// Removes all elements `e` for which `predicate(&e)` returns `false`. This method operates
	/// in-place, visiting each element exactly once in the original order, and preserves the order
	/// of the retained elements.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque = Deque::from([1, 2, 3, 4]);
	/// let mut unique = deque.as_unique();
	/// unique.retain(|&x| x % 2 == 0);
	/// assert_eq!(unique, [2, 4]);
	/// ```
	pub fn retain<F: FnMut(&T) -> bool>(&mut self, predicate: F) {
		delegate!(self.try_retain(predicate) -> shared);
	}
	/// Retains the elements specified by `predicate`, dropping the rest.
	///
	/// Removes all elements `e` for which `predicate(&mut e)` returns `false`. This method operates
	/// in-place, visiting each element exactly once in the original order, and preserves the order
	/// of the retained elements.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque = Deque::from([1, 2, 3, 4]);
	/// let mut unique = deque.as_unique();
	/// unique.retain_mut(|x| if *x % 2 == 0 {
	///     *x += 1;
	///     true
	/// } else {
	///     false
	/// });
	/// assert_eq!(unique, [3, 5]);
	/// ```
	pub fn retain_mut<F: FnMut(&mut T) -> bool>(&mut self, predicate: F) {
		delegate!(self.try_retain_mut(predicate) -> shared);
	}

	/// Moves all elements from `other` into this deque, leaving `other` empty. Any like[^atomic]
	/// unique collection type from this crate may be appended, even array collections with a
	/// different fixed capacity.
	///
	/// [^atomic]: the only restriction is that both collections must either be atomic or non-atomic;
	/// atomic collections may be only appended to other atomic collections, non-atomic vectors may
	/// only be appended to other non-atomic collections. 
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque = Deque::from([1, 2, 3]);
	/// let mut unique = deque.as_unique();
	///
	/// let mut deque2 = Deque::from([4, 5, 6]);
	/// unique.append(&mut deque2.as_unique());
	/// assert_eq!(unique, [1, 2, 3, 4, 5, 6]);
	/// assert_eq!(deque2, []);
	/// ```
	pub fn append<V: UniqueVector<T, A, ATOMIC> + ?Sized>(&mut self, other: &mut V) {
		delegate!(self.try_append(other) -> shared);
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
	/// let mut deque = Deque::from([1, 2, 3, 4, 5, 6, 7, 8]);
	/// let mut unique = deque.as_unique();
	/// let removed = unique.drain(2..6);
	/// assert!(removed.eq([3, 4, 5, 6]));
	/// assert_eq!(unique, [1, 2, 7, 8]);
	/// ```
	pub fn drain<R: RangeBounds<usize>>(&mut self, range: R) -> Drain<T, A, ATOMIC> {
		delegate!(self.try_drain(range) -> shared)
	}

	/// Clears the deque, removing all values.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque = Deque::from([1, 2, 3]);
	/// let mut unique = deque.as_unique();
	/// unique.clear();
	///
	/// assert_eq!(unique, []);
	/// ```
	pub fn clear(&mut self) {
		delegate!(mut self.clear());
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
	/// [`mem::take`]: core::mem::take
	/// [`mem::replace`]: core::mem::replace
	/// [`truncate`]: Self::truncate
	/// [`drain`]: Self::drain
	///
	/// # Panics
	///
	/// Panics if `at` is greater than the deque length.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque = Deque::from([1, 2, 3, 4]);
	/// let mut unique = deque.as_unique();
	/// assert_eq!(unique.split_off(2), [3, 4]);
	/// assert_eq!(unique, [1, 2]);
	/// ```
	#[must_use = "use `.truncate()` if you don't need the other half"]
	pub fn split_off(&mut self, at: usize) -> Deque<T, ATOMIC, A> where A: Clone {
		delegate!(self.try_split_off(at) -> shared)
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
	/// [`resize`]: Self::resize
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque = Deque::from([1, 2, 3]);
	/// let mut unique = deque.as_unique();
	/// let fill = Default::default;
	///
	/// unique.resize_with(5, fill);
	/// assert_eq!(unique, [1, 2, 3, 0, 0]);
	/// unique.resize_with(3, fill);
	/// assert_eq!(unique, [1, 2, 3]);
	/// ```
	pub fn resize_with<F: FnMut() -> T>(&mut self, new_len: usize, fill: F) {
		delegate!(self.try_resize_with(new_len, fill) -> shared);
	}

	/// Rearranges the contents of the deque such that they are stored in a single contiguous slice,
	/// returning the slice. The order of the elements in the deque is preserved; only the internal
	/// storage is changed.
	///
	/// Once the internal storage is contiguous, the [`as_slices`] and [`as_mut_slices`] will return
	/// the entire contents of the deque in a single slice. If this operation succeeds, the deque is
	/// always unique until cloned.
	///
	/// [`as_slices`]: Self::as_slices
	/// [`as_mut_slices`]: Self::as_mut_slices
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque = Deque::with_capacity(3);
	/// let mut unique = deque.as_unique();
	///
	/// unique.push_back(2);
	/// unique.push_back(1);
	/// unique.push_front(3);
	/// assert_eq!(unique.as_slices(), (&[2, 1][..], &[3][..]));
	///
	/// unique.make_contiguous();
	/// assert_eq!(unique.as_slices(), (&[3, 2, 1][..], &[][..]));
	/// ```
	pub fn make_contiguous(&mut self) -> &mut [T] {
		delegate!(self.try_make_contiguous() -> shared)
	}

	/// Rotates the deque contents `n` places to the left, such that the element at index `n` is the
	/// first element. This is equivalent to rotating right by `len() - n`.
	///
	/// # Panics
	///
	/// Panics if `n` is greater than the length of the deque. When `n` is equal to the length, this
	/// operation simply does nothing *without* panicking.
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
	/// let mut deque = (0..10).collect::<Deque<_>>();
	/// let mut unique = deque.as_unique();
	///
	/// unique.rotate_left(3);
	/// assert_eq!(unique, [3, 4, 5, 6, 7, 8, 9, 0, 1, 2]);
	///
	/// for i in 1..10 {
	///     assert_eq!(i * 3 % 10, unique[0]);
	///     unique.rotate_left(3);
	/// }
	/// assert_eq!(unique, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]);
	/// ```
	pub fn rotate_left(&mut self, n: usize) {
		delegate!(self.try_rotate_left(n) -> shared);
	}
	/// Rotates the deque contents `n` places to the right, such that the first element is at index
	/// `n`. This is equivalent to rotating left by `len() - n`.
	///
	/// # Panics
	///
	/// Panics if `n` is greater than the length of the deque. When `n` is equal to the length, this
	/// operation simply does nothing *without* panicking.
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
	/// let mut deque = (0..10).collect::<Deque<_>>();
	/// let mut unique = deque.as_unique();
	///
	/// unique.rotate_right(3);
	/// assert_eq!(unique, [7, 8, 9, 0, 1, 2, 3, 4, 5, 6]);
	///
	/// for i in 1..10 {
	///     assert_eq!(0, unique[i * 3 % 10]);
	///     unique.rotate_right(3);
	/// }
	/// assert_eq!(unique, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]);
	/// ```
	pub fn rotate_right(&mut self, n: usize) {
		delegate!(self.try_rotate_right(n) -> shared);
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
	/// let mut deque = Deque::from([0, 1, 1, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55]);
	/// let unique = deque.as_unique();
	///
	/// assert_eq!(unique.binary_search(&13),  Ok(9));
	/// assert_eq!(unique.binary_search(&4),   Err(7));
	/// assert_eq!(unique.binary_search(&100), Err(13));
	/// let r = unique.binary_search(&1);
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
	/// let mut unique = deque.as_unique();
	/// let num = 42;
	/// let idx = unique.partition_point(|&x| x <= num);
	/// // If `num` is unique, `s.partition_point(|&x| x < num)` (with `<`) is equivalent to
	/// // `s.binary_search(&num).unwrap_or_else(|x| x)`, but using `<=` may allow `insert`
	/// // to shift less elements.
	/// unique.insert(idx, num);
	/// assert_eq!(unique, [0, 1, 1, 1, 1, 2, 3, 5, 8, 13, 21, 34, 42, 55]);
	/// ```
	#[allow(clippy::missing_errors_doc)]
	pub fn binary_search(&self, x: &T) -> Result<usize, usize>
	where
		T: Ord,
	{
		delegate!(self.binary_search(x))
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
	/// let mut deque = Deque::from([0, 1, 1, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55]);
	/// let unique = deque.as_unique();
	///
	/// assert_eq!(unique.binary_search_by(|x| x.cmp(&13)),  Ok(9));
	/// assert_eq!(unique.binary_search_by(|x| x.cmp(&4)),   Err(7));
	/// assert_eq!(unique.binary_search_by(|x| x.cmp(&100)), Err(13));
	/// let r = unique.binary_search_by(|x| x.cmp(&1));
	/// assert!(matches!(r, Ok(1..=4)));
	/// ```
	#[allow(clippy::missing_errors_doc)]
	pub fn binary_search_by<F>(&self, compare: F) -> Result<usize, usize>
	where
		F: FnMut(&T) -> Ordering,
	{
		delegate!(self.binary_search_by(compare))
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
	/// let mut deque = Deque::from([
	///     (0, 0), (2, 1), (4, 1), (5, 1), (3, 1),
	///     (1, 2), (2, 3), (4, 5), (5, 8), (3, 13),
	///     (1, 21), (2, 34), (4, 55)
	/// ]);
	/// let unique = deque.as_unique();
	///
	/// assert_eq!(unique.binary_search_by_key(&13, |&(a, b)| b),  Ok(9));
	/// assert_eq!(unique.binary_search_by_key(&4, |&(a, b)| b),   Err(7));
	/// assert_eq!(unique.binary_search_by_key(&100, |&(a, b)| b), Err(13));
	/// let r = unique.binary_search_by_key(&1, |&(a, b)| b);
	/// assert!(matches!(r, Ok(1..=4)));
	/// ```
	#[allow(clippy::missing_errors_doc)]
	pub fn binary_search_by_key<B, F>(&self, key: &B, map: F) -> Result<usize, usize>
	where
		F: FnMut(&T) -> B,
		B: Ord,
	{
		delegate!(self.binary_search_by_key(key, map))
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
	/// let mut deque = Deque::from([1, 2, 3, 3, 5, 6, 7]);
	/// let unique = deque.as_unique();
	/// let i = unique.partition_point(|&x| x < 5);
	///
	/// assert_eq!(i, 4);
	/// assert!(unique.iter().take(i).all(|&x| x < 5));
	/// assert!(unique.iter().skip(i).all(|&x| !(x < 5)));
	/// ```
	///
	/// If you want to insert an item to a sorted deque, while maintaining sort order:
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque = Deque::from([0, 1, 1, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55]);
	/// let mut unique = deque.as_unique();
	/// let num = 42;
	/// let idx = unique.partition_point(|&x| x < num);
	/// unique.insert(idx, num);
	/// assert_eq!(unique, [0, 1, 1, 1, 1, 2, 3, 5, 8, 13, 21, 34, 42, 55]);
	/// ```
	pub fn partition_point<P>(&self, pred: P) -> usize
	where
		P: FnMut(&T) -> bool,
	{
		delegate!(self.partition_point(pred))
	}

	/// Converts the deque into a fixed-capacity deque of capacity `N`.
	///
	/// This operation takes *O*(1) time, and does not allocate memory.
	pub fn into_array_deque(self) -> Deque<T, ATOMIC, A> {
		todo!()
	}
}

impl<T: Clone, A: Allocator, const ATOMIC: bool> Unique<'_, T, A, ATOMIC> {
	/// Resizes the deque in-place to the specified length, cloning `value` into additional space
	/// as needed.
	///
	/// If `new_len` is greater than the current length, the deque is extended, filling the
	/// additional space with `value`. If `new_len` is less than the current length, the deque is
	/// truncated.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque = Deque::from([1, 2, 3]);
	/// let mut unique = deque.as_unique();
	///
	/// unique.resize(5, 0);
	/// assert_eq!(unique, [1, 2, 3, 0, 0]);
	/// unique.resize(3, 0);
	/// assert_eq!(unique, [1, 2, 3]);
	/// ```
	pub fn resize(&mut self, new_len: usize, value: T) {
		delegate!(self.try_resize(new_len, value) -> shared);
	}

	/// Clones and appends all elements in a slice to the back of the deque.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque = Deque::new();
	/// let mut unique = deque.as_unique();
	/// unique.extend_from_slice(&[1, 2, 3]);
	/// assert_eq!(unique, [1, 2, 3]);
	/// ```
	pub fn extend_from_slice(&mut self, other: &[T]) {
		delegate!(self.try_extend_from_slice(other) -> shared);
	}
	/// Clones and appends elements from `range` to the end of the back of the deque.
	///
	/// # Panics
	///
	/// Panics if the start of the range is greater than the end or if the end of the range is
	/// greater than the length of the deque.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut deque = Deque::from([1, 2, 3, 4]);
	/// let mut unique = deque.as_unique();
	/// unique.extend_from_within(1..3);
	/// assert_eq!(unique, [1, 2, 3, 4, 2, 3]);
	/// ```
	pub fn extend_from_within<R: RangeBounds<usize>>(&mut self, range: R) {
		delegate!(self.try_extend_from_within(range) -> shared);
	}
}

impl<T, A: Allocator, const ATOMIC: bool> Unique<'_, T, A, ATOMIC> {
	const fn as_inner(&self) -> &Deque<T, ATOMIC, A> {
		todo!()
	}

	pub(crate) const fn as_inner_mut(&mut self) -> &mut Deque<T, ATOMIC, A> {
		todo!()
	}
}

impl<'a, T, A: Allocator, const ATOMIC: bool> Unique<'a, T, A, ATOMIC> {
	fn into_inner(self) -> &'a mut Deque<T, ATOMIC, A> {
		todo!()
	}
}

impl<T: Hash, A: Allocator, const ATOMIC: bool> Hash for Unique<'_, T, A, ATOMIC> {
	fn hash<H: Hasher>(&self, state: &mut H) {
		self.as_inner().hash(state)
	}
}

impl<T, A: Allocator, const ATOMIC: bool> Index<usize> for Unique<'_, T, A, ATOMIC> {
	type Output = T;

	fn index(&self, index: usize) -> &Self::Output {
		self.as_inner().index(index)
	}
}

impl<T, A: Allocator, const ATOMIC: bool> IndexMut<usize> for Unique<'_, T, A, ATOMIC> {
	fn index_mut(&mut self, index: usize) -> &mut Self::Output {
		self.get_mut(index).expect("Out of bounds access")
	}
}

impl<'a, T: 'a, A: Allocator + 'a, const ATOMIC: bool> IntoIterator for Unique<'a, T, A, ATOMIC> {
	type Item = T;
	type IntoIter = Drain<'a, T, A, ATOMIC>;

	/// Consumes the unique wrapper into a front-to-back iterator yielding elements by value. If the
	/// deque is shared, the elements are cloned out of the deque.
	fn into_iter(self) -> Self::IntoIter {
		// Safety: this type already upholds uniqueness as an invariant
		unsafe {
			self.into_inner()
				.try_drain(..)
				.unwrap_unchecked()
		}
	}
}

impl<'a, T, A: Allocator, const ATOMIC: bool> IntoIterator for &'a Unique<'_, T, A, ATOMIC> {
	type Item = &'a T;
	type IntoIter = Iter<'a, T>;

	fn into_iter(self) -> Self::IntoIter {
		self.iter()
	}
}

impl<'a, T, A: Allocator, const ATOMIC: bool> IntoIterator for &'a mut Unique<'_, T, A, ATOMIC> {
	type Item = &'a mut T;
	type IntoIter = IterMut<'a, T>;

	fn into_iter(self) -> Self::IntoIter {
		self.iter_mut()
	}
}

impl<T, A: Allocator, const ATOMIC: bool> Extend<T> for Unique<'_, T, A, ATOMIC> {
	fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
		delegate!(self.try_extend(iter) -> shared);
	}

	#[cfg(feature = "unstable-traits")]
	fn extend_reserve(&mut self, additional: usize) {
		delegate!(self.try_reserve(additional) -> shared);
	}

	#[cfg(feature = "unstable-traits")]
	fn extend_one(&mut self, item: T) {
		self.push_back(item);
	}
}

impl<'a, T: Copy + 'a, A: Allocator, const ATOMIC: bool> Extend<&'a T> for Unique<'_, T, A, ATOMIC> {
	fn extend<I: IntoIterator<Item = &'a T>>(&mut self, iter: I) {
		delegate!(self.try_extend_ref(iter) -> shared);
	}

	#[cfg(feature = "unstable-traits")]
	fn extend_reserve(&mut self, additional: usize) {
		delegate!(self.try_reserve(additional) -> shared);
	}

	#[cfg(feature = "unstable-traits")]
	fn extend_one(&mut self, item: &'a T) {
		self.extend_one(*item);
	}
}

impl<T: Eq, A: Allocator, const ATOMIC: bool> Eq for Unique<'_, T, A, ATOMIC> { }

impl<T, A1, A2, const ATOMIC1: bool, const ATOMIC2: bool> PartialOrd<Unique<'_, T, A2, ATOMIC2>> for Unique<'_, T, A1, ATOMIC1>
where
	T: PartialOrd,
	A1: Allocator,
	A2: Allocator
{
	fn partial_cmp(&self, other: &Unique<'_, T, A2, ATOMIC2>) -> Option<Ordering> {
		PartialOrd::partial_cmp(self.as_inner(), other.as_inner())
	}
}

impl<T: Ord, A: Allocator, const ATOMIC: bool> Ord for Unique<'_, T, A, ATOMIC> {
	fn cmp(&self, other: &Self) -> Ordering {
		Ord::cmp(self.as_inner(), other.as_inner())
	}
}

impl<T: fmt::Debug, A: Allocator, const ATOMIC: bool> fmt::Debug for Unique<'_, T, A, ATOMIC> {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		fmt::Debug::fmt(self.as_inner(), f)
	}
}
