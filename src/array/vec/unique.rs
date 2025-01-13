// Copyright 2025 - Strixpyrr
// SPDX-License-Identifier: Apache-2.0

use core::alloc::Allocator;
use core::cmp::Ordering;
use core::hash::{Hash, Hasher};
use core::fmt;
use core::marker::PhantomData;
use core::mem::MaybeUninit;
use core::ops::{Deref, DerefMut, Index, IndexMut, RangeBounds};
use core::ptr::NonNull;
use core::slice::{Iter, IterMut, SliceIndex};
use crate::array::{FullCapacity, TryExtend, TryExtendIter, TryInsert};
use crate::array::macros::*;
use crate::marker::UniqueVector;
use super::{ArrayVec, Drain};

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
/// mutability on a shared vector. Before this wrapper is created, any weak references will be first
/// disassociated with the vector contents.
pub struct Unique<
	'a,
	T: 'a,
	const N: usize,
	A: Allocator + 'a,
	const ATOMIC: bool
> {
	_ref: PhantomData<&'a mut ArrayVec<T, N, ATOMIC, A>>,
}

impl<T, const N: usize, A: Allocator, const ATOMIC: bool> Unique<'_, T, N, A, ATOMIC> {
	/// The fixed capacity of the vector.
	pub const CAPACITY: usize = N;

	/// Consumes the reference, returning a vector with a shared reference.
	pub fn into_shared(self) -> ArrayVec<T, N, ATOMIC, A> where A: Clone {
		delegate!(self.clone())
	}

	/// Returns the total number of elements the vector can hold.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::vec::rc::{ArrayVec, Unique};
	///
	/// let mut vec = ArrayVec::new();
	/// let mut unique: Unique<i32, 8> = vec.as_unique();
	/// assert_eq!(unique.capacity(), 8);
	/// ```
	#[inline(always)]
	pub const fn capacity(&self) -> usize {
		Self::CAPACITY
	}

	/// Returns the number of elements the vector can hold before filled. This is shorthand for
	/// `N - length`.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::vec::rc::{ArrayVec, Unique};
	///
	/// let mut vec = ArrayVec::new();
	/// let mut unique: Unique<i32, 8> = vec.as_unique();
	/// unique.extend([1, 2, 3]);
	///
	/// assert_eq!(unique.limit(), 5);
	///
	/// unique.extend([0; 5]);
	/// assert_eq!(unique.limit(), 0);
	/// ```
	pub const fn limit(&self) -> usize {
		delegate!(self.limit())
	}

	/// Shortens the vector, keeping the first `len` elements and dropping the rest. If `len` is
	/// greater or equal to the vector's current length, this has no effect.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::vec::rc::{ArrayVec, Unique};
	///
	/// let mut vec = ArrayVec::from([1, 2, 3, 4, 5]);
	/// let mut unique: Unique<i32, 5> = vec.as_unique();
	/// // Truncates from 5 elements to 2
	/// unique.truncate(2);
	/// assert_eq!(unique, [1, 2]);
	/// // No truncation occurs when the length is greater than the vector's current length
	/// unique.truncate(8);
	/// assert_eq!(unique, [1, 2]);
	/// // Truncating to 0 elements is equivalent to `clear`
	/// unique.truncate(0);
	/// assert_eq!(unique, []);
	/// ```
	pub fn truncate(&mut self, len: usize) {
		delegate!(mut self.truncate(len));
	}

	/// Returns a slice over the vector contents.
	///
	/// Equivalent to `&s[..]`.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::vec::rc::{ArrayVec, Unique};
	///
	/// let mut vec = ArrayVec::new();
	/// let mut unique: Unique<i32, 8> = vec.as_unique();
	/// unique.extend([1, 2, 3]);
	///
	/// assert_eq!(unique.as_slice(), [1, 2, 3]);
	/// ```
	pub fn as_slice(&self) -> &[T] {
		delegate!(self.as_slice())
	}

	/// Returns a mutable slice over the vector contents.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::vec::rc::{ArrayVec, Unique};
	///
	/// let mut vec = ArrayVec::from([1, 2, 3, 4, 5, 6, 7, 8]);
	/// let mut unique: Unique<i32, 8> = vec.as_unique();
	/// unique.as_mut_slice().rotate_left(3);
	///
	/// assert_eq!(unique.as_slice(), [4, 5, 6, 7, 8, 1, 2, 3]);
	/// ```
	pub fn as_mut_slice(&mut self) -> &mut [T] {
		delegate!(self.try_as_mut_slice() -> shared)
	}

	/// Returns a raw pointer to the vector's buffer.
	///
	/// The caller must ensure that the vector outlives the pointer this function returns, or else
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
	/// This pointer remains valid even when the [`Unique`] wrapper goes out of scope, as long as
	/// the referenced vector remains in scope.
	///
	/// [`as_mut_ptr`]: Self::as_mut_ptr
	/// [`as_ptr`]: Self::as_ptr
	/// [`as_non_null`]: Self::as_non_null
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::vec::rc::{ArrayVec, Unique};
	///
	/// let mut vec = ArrayVec::from([1, 2, 4]);
	/// let unique: Unique<i32, 3> = vec.as_unique();
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
	/// use sharevec::array::vec::rc::{ArrayVec, Unique};
	///
	/// let mut vec = ArrayVec::from([1, 2, 3]);
	/// let mut unique: Unique<i32, 3> = vec.as_unique();
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
	/// Returns a raw pointer to the vector's buffer.
	///
	/// The caller must ensure that the vector outlives the pointer this function returns, or else
	/// it will end up dangling.
	///
	/// This method guarantees that for the purpose of the aliasing model, this method does not
	/// materialize a reference to the underlying slice, and thus the returned pointer will remain
	/// valid when mixed with other calls to [`as_ptr`], [`as_mut_ptr`], and [`as_non_null`]. Note
	/// that calling other methods that materialize mutable references to the slice, or mutable
	/// references to specific elements you are planning on accessing through this pointer, as well
	/// as writing to those elements, may still invalidate this pointer.
	///
	/// This pointer remains valid even when the [`Unique`] wrapper goes out of scope, as long as
	/// the referenced vector remains in scope. Once this wrapper is dropped, the same mutability
	/// rules as [`ArrayVec::as_mut_ptr`] apply.
	///
	/// [`as_mut_ptr`]: Self::as_mut_ptr
	/// [`as_ptr`]: Self::as_ptr
	/// [`as_non_null`]: Self::as_non_null
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::vec::rc::{ArrayVec, Unique};
	///
	/// let mut vec = ArrayVec::new();
	/// let mut unique: Unique<i32, 8> = vec.as_unique();
	/// let ptr = unique.as_mut_ptr();
	///
	/// // Initialize elements via raw pointer writes, then set length.
	/// // This is safe because no other strong reference points to the vector contents.
	/// unsafe {
	///     for i in 0..unique.capacity() {
	///         ptr.add(i).write(i as i32);
	///     }
	///     unique.set_len(8);
	/// }
	/// assert_eq!(unique, [1, 2, 3, 4, 5, 6, 7, 8]);
	/// ```
	///
	/// Due to the aliasing guarantee, this code is valid:
	///
	/// ```
	/// use sharevec::array::vec::rc::{ArrayVec, Unique};
	///
	/// let mut vec = ArrayVec::from([0]);
	/// let mut unique: Unique<i32, 1> = vec.as_unique();
	/// unsafe {
	///     let ptr1 = unique.as_mut_ptr();
	///     ptr1.write(1);
	///     let ptr2 = unique.as_mut_ptr();
	///     ptr2.write(2);
	///     // Notably, writing to `ptr2` did *not* invalidate `ptr1`:
	///     ptr1.write(3);
	/// }
	/// ```
	pub fn as_mut_ptr(&mut self) -> *mut T {
		delegate!(mut self.as_mut_ptr())
	}
	/// Returns a `NonNull` pointer to the vector's buffer.
	///
	/// The caller must ensure that the vector outlives the pointer this function returns, or else
	/// will end up dangling.
	///
	/// This method guarantees that for the purpose of the aliasing model, this method does not
	/// materialize a reference to the underlying slice, and thus the returned pointer will remain
	/// valid when mixed with other calls to [`as_ptr`], [`as_mut_ptr`], and [`as_non_null`]. Note
	/// that calling other methods that materialize mutable references to the slice, or mutable
	/// references to specific elements you are planning on accessing through this pointer, as well
	/// as writing to those elements, may still invalidate this pointer.
	///
	/// This pointer remains valid even when the [`Unique`] wrapper goes out of scope, as long as
	/// the referenced vector remains in scope. Once this wrapper is dropped, the same mutability
	/// rules as [`ArrayVec::as_mut_ptr`] apply.
	///
	/// [`as_mut_ptr`]: Self::as_mut_ptr
	/// [`as_ptr`]: Self::as_ptr
	/// [`as_non_null`]: Self::as_non_null
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::vec::rc::{ArrayVec, Unique};
	///
	/// let mut vec = ArrayVec::new();
	/// let mut unique: Unique<i32, 8> = vec.as_unique();
	/// let ptr = unique.as_non_null();
	///
	/// // Initialize elements via raw pointer writes, then set length.
	/// // This is safe because no other strong reference points to the vector contents.
	/// unsafe {
	///     for i in 0..unique.capacity() {
	///         ptr.add(i).write(i as i32);
	///     }
	///     unique.set_len(8);
	/// }
	/// assert_eq!(unique, [1, 2, 3, 4, 5, 6, 7, 8]);
	/// ```
	///
	/// Due to the aliasing guarantee, this code is valid:
	///
	/// ```
	/// use sharevec::array::vec::rc::{ArrayVec, Unique};
	///
	/// let mut vec = ArrayVec::from([0]);
	/// let mut unique: Unique<i32, 1> = vec.as_unique();
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
	/// `new_len` must be less than or equal to the fixed capacity, `N`. The elements from the old
	/// length to `new_len` must be initialized.
	///
	/// # Examples
	///
	/// See [`spare_capacity_mut`] for an example with safe initialization of capacity elements and
	/// use of this method.
	///
	/// [`spare_capacity_mut`]: Self::spare_capacity_mut
	pub unsafe fn set_len(&mut self, new_len: usize) {
		delegate!(mut self.set_len(new_len));
	}

	/// Removes and returns the element at position `index` from the vector, replacing this element
	/// with the last element in the vector. This doesn't preserve ordering of the remaining
	/// elements, but is *O*(1). If ordering must be preserved, use [`remove`].
	///
	/// [`remove`]: Self::remove
	///
	/// # Panics
	///
	/// Panics if `index` is greater than the vector length.
	///
	/// # Time complexity
	///
	/// Takes *O*(1) time.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec = ArrayVec::from(['a', 'b', 'c', 'd']);
	/// let mut unique = vec.as_unique();
	///
	/// assert_eq!(unique.swap_remove(1), 'b');
	/// assert_eq!(unique, ['a', 'd', 'c']);
	///
	/// assert_eq!(unique.swap_remove(0), 'a');
	/// assert_eq!(unique, ['c', 'd']);
	/// ```
	pub fn swap_remove(&mut self, index: usize) -> T {
		delegate!(self.try_swap_remove(index) -> shared)
	}

	/// Removes and returns the element at position `index` from the vector, shifting all subsequent
	/// elements to the left.
	///
	/// # Panics
	///
	/// Panics if `index` is greater than the vector length.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec = ArrayVec::from(['a', 'b', 'c']);
	/// let mut unique = vec.as_unique();
	/// assert_eq!(unique.remove(1), 'b');
	/// assert_eq!(unique, ['a', 'c']);
	/// ```
	///
	/// # Time complexity
	///
	/// Takes at most *O*(*n*) time, as all elements after `index` must be shifted. In the worst
	/// case, all [`len`] elements must be shifted when `index` is `0`. If element ordering is not
	/// important, use [`swap_remove`] instead, which is *O*(1). If you need to remove elements from
	/// the beginning of the vector frequently and need to preserve ordering, consider
	/// [`ArcArrayDeque::try_pop_front`], which is also *O*(1).
	///
	/// [`len`]: Self::len
	/// [`swap_remove`]: Self::swap_remove
	/// [`ArcArrayDeque::try_pop_front`]: crate::array::deque::arc::ArrayDeque::try_pop_front
	pub fn remove(&mut self, index: usize) -> T {
		delegate!(self.try_remove(index) -> shared)
	}

	/// Insert an element at position `index` within the vector, shifting all subsequent elements to
	/// the right.
	///
	/// # Errors
	///
	/// Returns an error containing the element if the vector is full.
	///
	/// # Panics
	///
	/// Panics if `index` is greater than the vector length.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::vec::rc::{ArrayVec, Unique};
	///
	/// let mut vec = ArrayVec::new();
	/// let mut unique: Unique<char, 4> = vec.as_unique();
	/// unique.extend(['a', 'c']);
	///
	/// assert_eq!(unique.insert(1, 'b'), Ok(()));
	/// assert_eq!(unique, ['a', 'b', 'c']);
	/// assert_eq!(unique.insert(3, 'd'), Ok(()));
	/// assert_eq!(unique, ['a', 'b', 'c', 'd']);
	/// assert_eq!(unique.insert(0, 'e'), Err('e'));
	/// ```
	///
	/// # Time complexity
	///
	/// Takes at most *O*(*n*) time, as all elements after `index` must be shifted. In the worst
	/// case, all [`len`] elements must be shifted when `index` is `0`.
	///
	/// [`len`]: Self::len
	pub fn insert(&mut self, index: usize, element: T) -> Result<(), T> {
		delegate!(self.try_insert(index, element) -> insert)
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
	/// use sharevec::array::vec::rc::{ArrayVec, Unique};
	///
	/// let mut vec = ArrayVec::from([1, 2, 3, 4]);
	/// let mut unique: Unique<i32, 4> = vec.as_unique();
	/// unique.retain(|&x| x % 2 == 0);
	/// assert_eq!(unique, [2, 4]);
	/// ```
	pub fn retain<F: FnMut(&T) -> bool>(&mut self, predicate: F) {
		delegate!(self.try_retain(predicate) -> shared)
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
	/// use sharevec::array::vec::rc::{ArrayVec, Unique};
	///
	/// let mut vec = ArrayVec::from([1, 2, 3, 4]);
	/// let mut unique: Unique<i32, 4> = vec.as_unique();
	/// unique.retain_mut(|x| if *x % 2 == 0 {
	///     *x += 1;
	///     true
	/// } else {
	///     false
	/// });
	/// assert_eq!(unique, [3, 5]);
	/// ```
	pub fn retain_mut<F: FnMut(&mut T) -> bool>(&mut self, predicate: F) {
		delegate!(self.try_retain_mut(predicate) -> shared)
	}

	/// Removes consecutive repeated elements from the vector according to the [`PartialEq`] trait
	/// implementation. If the vector is sorted, all duplicates are removed.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::vec::rc::{ArrayVec, Unique};
	///
	/// let mut vec = ArrayVec::from([1, 2, 2, 3, 2]);
	/// let mut unique: Unique<i32, 5> = vec.as_unique();
	/// unique.dedup();
	/// assert_eq!(unique, [1, 2, 3, 2]);
	/// ```
	pub fn dedup(&mut self) where T: PartialEq {
		delegate!(self.try_dedup() -> shared)
	}
	/// Removes consecutive repeated elements from the vector that resolve to the same key given by
	/// `key`. If the vector is sorted, all duplicates are removed.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::vec::rc::{ArrayVec, Unique};
	///
	/// let mut vec = ArrayVec::from([10, 20, 21, 30, 20]);
	/// let mut unique: Unique<i32, 5> = vec.as_unique();
	/// unique.dedup_by_key(|&mut x| x / 10);
	/// assert_eq!(unique, [10, 20, 30, 20]);
	/// ```
	pub fn dedup_by_key<F: FnMut(&mut T) -> K, K: PartialEq>(&mut self, key: F) {
		delegate!(self.try_dedup_by_key(key) -> shared)
	}
	/// Removes consecutive repeated elements from the vector that satisfy an equality `predicate`.
	/// If the vector is sorted, all duplicates are removed.
	///
	/// The `predicate` function is passed references to two elements from the vector and determines
	/// if the elements are equal. The elements are passed in opposite order, such that if
	/// `predicate(a, b)` returns `true`, element `a` is removed.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::vec::rc::{ArrayVec, Unique};
	///
	/// let mut vec = ArrayVec::from(['a', 'A', 'b', 'c', 'c', 'B']);
	/// let mut unique: Unique<char, 6> = vec.as_unique();
	/// unique.dedup_by(|a, b| a.eq_ignore_ascii_case(b));
	/// assert_eq!(unique, ['a', 'b', 'c', 'B']);
	/// ```
	pub fn dedup_by<F: FnMut(&mut T, &mut T) -> bool>(&mut self, predicate: F) {
		delegate!(self.try_dedup_by(predicate) -> shared)
	}

	/// Appends an element to the end of the vector if there is sufficient spare capacity, otherwise
	/// returns an error containing the element.
	///
	/// # Errors
	///
	/// Returns an error containing the element if the vector is full.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::vec::rc::{ArrayVec, Unique};
	///
	/// let mut vec = ArrayVec::new();
	/// let mut unique: Unique<i32, 2> = vec.as_unique();
	/// assert_eq!(unique.push(1), Ok(()));
	/// assert_eq!(unique.push(2), Ok(()));
	/// assert_eq!(unique.push(3), Err(3));
	/// ```
	///
	/// # Time complexity
	///
	/// Takes *O*(1) time.
	pub fn push(&mut self, value: T) -> Result<(), T> {
		delegate!(self.try_push(value) -> insert)
	}

	/// Removes and returns the last element from the vector, or [`None`] if it is empty.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::vec::rc::{ArrayVec, Unique};
	///
	/// let mut vec = ArrayVec::from([1, 2]);
	/// let mut unique: Unique<i32, 2> = vec.as_unique();
	/// assert_eq!(unique.pop(), Some(2));
	/// assert_eq!(unique.pop(), Some(1));
	/// assert_eq!(unique.pop(), None);
	/// ```
	///
	/// # Time complexity
	///
	/// Takes *O*(1) time.
	pub fn pop(&mut self) -> Option<T> {
		delegate!(self.try_pop() -> shared)
	}

	/// Removes and returns the last element from the vector if the predicate returns `true`, or
	/// `None` if predicate returns `false` or the vector is empty. If the vector is empty, the
	/// predicate is not called.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec = ArrayVec::from([1, 2, 3, 4]);
	/// let mut unique = vec.as_unique();
	/// let even = |x: &mut i32| *x % 2 == 0;
	/// assert_eq!(unique.pop_if(even), Some(4));
	/// assert_eq!(unique, [1, 2, 3]);
	/// assert_eq!(unique.pop_if(even), None);
	/// ```
	///
	/// # Time complexity
	///
	/// Takes *O*(1) time.
	pub fn pop_if<F: FnOnce(&mut T) -> bool>(&mut self, predicate: F) -> Option<T> {
		todo!()
	}

	/// Moves all elements from `other` into this vector, leaving `other` empty. Any like[^atomic]
	/// unique vector type from this crate may be appended, even array vectors with a different fixed
	/// capacity.
	/// 
	/// [^atomic]: the only restriction is that both vectors must either be atomic or non-atomic;
	/// atomic vectors may be only appended to other atomic vectors, non-atomic vectors may only be
	/// appended to other non-atomic vectors. 
	///
	/// # Errors
	///
	/// Returns an error if the vector would overflow its fixed capacity after appending `other`. In
	/// this case, neither vector is modified.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::FullCapacity;
	/// use sharevec::array::vec::rc::{ArrayVec, Unique};
	///
	/// let mut vec = ArrayVec::new();
	/// vec.extend([1, 2, 3]);
	/// let mut unique: Unique<i32, 7> = vec.as_unique();
	/// let mut vec2 = ArrayVec::from([4, 5, 6]);
	/// let mut vec3 = ArrayVec::from([7, 8, 9]);
	/// assert_eq!(unique.append(&mut vec2.as_unique()), Ok(()));
	/// assert_eq!(unique, [1, 2, 3, 4, 5, 6]);
	/// assert_eq!(vec2, []);
	///
	/// assert_eq!(unique.append(&mut vec3.as_unique()), Err(FullCapacity { remaining: 2 }));
	/// assert_eq!(unique, [1, 2, 3, 4, 5, 6, 7]);
	/// assert_eq!(vec3, [8, 9]);
	/// ```
	pub fn append<V: UniqueVector<T, A, ATOMIC> + ?Sized>(&mut self, other: &mut V) -> Result<(), FullCapacity> {
		delegate!(self.try_append(other) -> extend)
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
	/// use sharevec::array::vec::rc::{ArrayVec, Unique};
	///
	/// let mut vec = ArrayVec::from([1, 2, 3, 4, 5, 6, 7, 8]);
	/// let mut unique: Unique<i32, 8> = vec.as_unique();
	/// let removed = unique.drain(2..6);
	/// assert!(removed.eq([3, 4, 5, 6]));
	/// assert_eq!(unique, [1, 2, 7, 8]);
	/// ```
	pub fn drain<R: RangeBounds<usize>>(&mut self, range: R) -> Drain<T, N, A, ATOMIC> {
		delegate!(self.try_drain(range) -> shared)
	}

	/// Clears the vector, removing all values.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::vec::rc::{ArrayVec, Unique};
	///
	/// let mut vec = ArrayVec::from([1, 2, 3]);
	/// let mut unique: Unique<i32, 3> = vec.as_unique();
	/// unique.clear();
	///
	/// assert_eq!(unique, []);
	/// ```
	pub fn clear(&mut self) {
		delegate!(mut self.clear());
	}

	/// Returns the number of elements in the vector.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec = ArrayVec::from([1, 2, 3]);
	/// let unique = vec.as_unique();
	/// assert_eq!(unique.len(), 3);
	/// ```
	pub fn len(&self) -> usize {
		delegate!(self.len())
	}
	/// Returns `true` if the vector contains no elements.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::vec::rc::{ArrayVec, Unique};
	///
	/// let mut vec = ArrayVec::new();
	/// let mut unique: Unique<i32, 1> = vec.as_unique();
	/// assert!(unique.is_empty());
	///
	/// _ = unique.push(1);
	/// assert!(!unique.is_empty());
	/// ```
	pub fn is_empty(&self) -> bool {
		delegate!(self.is_empty())
	}
	/// Returns `true` if the vector contains any elements.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::vec::rc::{ArrayVec, Unique};
	///
	/// let mut vec = ArrayVec::new();
	/// let mut unique: Unique<i32, 1> = vec.as_unique();
	/// assert!(!unique.is_not_empty());
	///
	/// _ = unique.push(1);
	/// assert!(unique.is_not_empty());
	/// ```
	pub fn is_not_empty(&self) -> bool {
		delegate!(self.is_not_empty())
	}
	/// Returns `true` if the vector cannot hold any more elements.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec = ArrayVec::from([1, 2, 3]);
	/// let mut unique = vec.as_unique();
	/// assert!(unique.is_full());
	///
	/// _ = unique.pop();
	/// assert!(!unique.is_full());
	/// ```
	pub fn is_full(&self) -> bool {
		delegate!(self.is_full())
	}
	/// Returns `true` if the vector can hold more elements.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec = ArrayVec::from([1, 2, 3]);
	/// let mut unique = vec.as_unique();
	/// assert!(!unique.is_not_full());
	///
	/// _ = unique.pop();
	/// assert!(unique.is_not_full());
	/// ```
	pub fn is_not_full(&self) -> bool {
		delegate!(self.is_not_full())
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
	/// [`mem::take`]: core::mem::take
	/// [`mem::replace`]: core::mem::replace
	/// [`truncate`]: Self::truncate
	/// [`drain`]: Self::drain
	///
	/// # Panics
	///
	/// Panics if `at` is greater than the vector length.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec = ArrayVec::from([1, 2, 3, 4]);
	/// let mut unique = vec.as_unique();
	/// assert_eq!(unique.split_off(2), [3, 4]);
	/// assert_eq!(unique, [1, 2]);
	/// ```
	#[must_use = "use `.truncate()` if you don't need the other half"]
	pub fn split_off(&mut self, at: usize) -> ArrayVec<T, N, ATOMIC, A>
	where A: Clone {
		delegate!(self.try_split_off(at) -> shared)
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
	/// [`resize`]: Self::resize
	///
	/// # Errors
	///
	/// Returns an error if the new length would be larger than the fixed capacity of the vector. In
	/// this case, the vector is filled completely.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::FullCapacity;
	/// use sharevec::array::vec::rc::{ArrayVec, Unique};
	///
	/// let mut vec = ArrayVec::new();
	/// let mut unique: Unique<i32, 8> = vec.as_unique();
	/// unique.extend([1, 2, 3]);
	/// let fill = Default::default;
	///
	/// assert_eq!(unique.resize_with(5, fill), Ok(()));
	/// assert_eq!(unique, [1, 2, 3, 0, 0]);
	/// assert_eq!(unique.resize_with(3, fill), Ok(()));
	/// assert_eq!(unique, [1, 2, 3]);
	/// assert_eq!(unique.resize_with(16, fill), Err(FullCapacity { remaining: 8 }));
	/// assert_eq!(unique, [1, 2, 3, 0, 0, 0, 0, 0]);
	/// ```
	pub fn resize_with<F: FnMut() -> T>(&mut self, new_len: usize, fill: F) -> Result<(), FullCapacity> {
		delegate!(self.try_resize_with(new_len, fill) -> extend)
	}

	/// Returns the remaining spare capacity of the vector as a slice of uninitialized elements.
	///
	/// The returned slice can be used to fill the vector, before marking the data as initialized
	/// with [`set_len`].
	///
	/// [`set_len`]: Self::set_len
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::vec::rc::{ArrayVec, Unique};
	///
	/// let mut vec = ArrayVec::new();
	/// let mut unique: Unique<i32, 10> = vec.as_unique();
	///
	/// let spare = unique.spare_capacity_mut();
	/// spare[0].write(0);
	/// spare[1].write(1);
	/// spare[2].write(2);
	///
	/// unsafe {
	///     unique.set_len(3);
	/// }
	///
	/// assert_eq!(unique, [0, 1, 2]);
	/// ```
	pub fn spare_capacity_mut(&mut self) -> &mut [MaybeUninit<T>] {
		delegate!(self.try_spare_capacity_mut() -> shared)
	}
}

// Todo: try_extend and try_extend_ref returning FullCapacity error.

impl<T: Clone, const N: usize, A: Allocator, const ATOMIC: bool> Unique<'_, T, N, A, ATOMIC> {
	/// Clones and appends all elements in a slice to the vector.
	///
	/// # Errors
	///
	/// Returns an error if the vector is filled before the full slice could be appended. In this
	/// case, the vector is filled completely and the error contains the number of elements
	/// remaining.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::FullCapacity;
	/// use sharevec::array::vec::rc::{ArrayVec, Unique};
	///
	/// let mut vec = ArrayVec::new();
	/// let mut unique: Unique<i32, 4> = vec.as_unique();
	/// assert_eq!(unique.extend_from_slice(&[1, 2, 3]), Ok(()));
	/// assert_eq!(unique.extend_from_slice(&[4, 5, 6]), Err(FullCapacity { remaining: 2 }));
	/// assert_eq!(unique, [1, 2, 3, 4]);
	/// ```
	pub fn extend_from_slice(&mut self, other: &[T]) -> Result<(), FullCapacity> {
		delegate!(self.try_extend_from_slice(other) -> extend)
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
	/// Returns an error if the vector is filled before the full range could be appended. In this
	/// case, the vector is filled completely and the error contains the number of elements
	/// remaining.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::FullCapacity;
	/// use sharevec::array::vec::rc::{ArrayVec, Unique};
	///
	/// let mut vec = ArrayVec::new();
	/// let mut unique: Unique<i32, 8> = vec.as_unique();
	/// unique.extend([1, 2, 3, 4]);
	/// assert_eq!(unique.extend_from_within(1..3), Ok(()));
	/// assert_eq!(unique, [1, 2, 3, 4, 2, 3]);
	/// assert_eq!(unique.extend_from_within(0..3), Err(FullCapacity { remaining: 1 }));
	/// assert_eq!(unique, [1, 2, 3, 4, 2, 3, 1, 2]);
	/// ```
	pub fn extend_from_within<R: RangeBounds<usize>>(&mut self, range: R) -> Result<(), FullCapacity> {
		delegate!(self.try_extend_from_within(range) -> extend)
	}

	/// Resizes the vector in-place to the specified length, cloning `value` into additional space
	/// as needed.
	///
	/// # Errors
	///
	/// Returns an error if the new length would be larger than the fixed capacity of the vector. In
	/// this case, the vector if filled completely.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::FullCapacity;
	/// use sharevec::array::vec::rc::{ArrayVec, Unique};
	///
	/// let mut vec = ArrayVec::new();
	/// let mut unique: Unique<i32, 8> = vec.as_unique();
	/// unique.extend([1, 2, 3]);
	///
	/// assert_eq!(unique.resize(5, 0), Ok(()));
	/// assert_eq!(unique, [1, 2, 3, 0, 0]);
	/// assert_eq!(unique.resize(3, 0), Ok(()));
	/// assert_eq!(unique, [1, 2, 3]);
	/// assert_eq!(unique.resize(16, 0), Err(FullCapacity { remaining: 8 }));
	/// assert_eq!(unique, [1, 2, 3, 0, 0, 0, 0, 0]);
	/// ```
	pub fn resize(&mut self, new_len: usize, value: T) -> Result<(), FullCapacity> {
		delegate!(self.try_resize(new_len, value) -> extend)
	}
}

impl<T, const N: usize, A: Allocator, const ATOMIC: bool> Unique<'_, T, N, A, ATOMIC> {
	const fn as_inner(&self) -> &ArrayVec<T, N, ATOMIC, A> {
		todo!()
	}

	const fn as_inner_mut(&mut self) -> &mut ArrayVec<T, N, ATOMIC, A> {
		todo!()
	}
}

impl<'a, T, const N: usize, A: Allocator, const ATOMIC: bool> Unique<'a, T, N, A, ATOMIC> {
	fn into_inner(self) -> &'a mut ArrayVec<T, N, ATOMIC, A> {
		todo!()
	}
}

impl<T, const N: usize, A: Allocator, const ATOMIC: bool> Deref for Unique<'_, T, N, A, ATOMIC> {
	type Target = [T];

	fn deref(&self) -> &[T] {
		self.as_inner()
	}
}

impl<T, const N: usize, A: Allocator, const ATOMIC: bool> DerefMut for Unique<'_, T, N, A, ATOMIC> {
	fn deref_mut(&mut self) -> &mut [T] {
		self.as_mut_slice()
	}
}

impl<T: Hash, const N: usize, A: Allocator, const ATOMIC: bool> Hash for Unique<'_, T, N, A, ATOMIC> {
	fn hash<H: Hasher>(&self, state: &mut H) {
		delegate!(self.hash(state));
	}
}

impl<T, const N: usize, I: SliceIndex<[T]>, A: Allocator, const ATOMIC: bool> Index<I> for Unique<'_, T, N, A, ATOMIC> {
	type Output = I::Output;

	fn index(&self, index: I) -> &Self::Output {
		delegate!(self.index(index))
	}
}

#[cfg(feature = "unstable-traits")]
impl<T, const N: usize, I: SliceIndex<[T]>, A: Allocator, const ATOMIC: bool> IndexMut<I> for Unique<'_, T, N, A, ATOMIC> {
	fn index_mut(&mut self, index: I) -> &mut Self::Output {
		delegate!(self.try_index_mut(index) -> shared)
	}
}

impl<'a, T, const N: usize, A: Allocator, const ATOMIC: bool> IntoIterator for Unique<'a, T, N, A, ATOMIC> {
	type Item = T;
	type IntoIter = Drain<'a, T, N, A, ATOMIC>;

	/// Consumes the vector into an iterator yielding elements by value.
	fn into_iter(self) -> Self::IntoIter {
		// Safety: this type already upholds uniqueness as an invariant
		unsafe {
			self.into_inner()
				.try_drain(..)
				.unwrap_unchecked()
		}
	}
}

impl<'a, T, const N: usize, A: Allocator, const ATOMIC: bool> IntoIterator for &'a Unique<'_, T, N, A, ATOMIC> {
	type Item = &'a T;
	type IntoIter = Iter<'a, T>;

	fn into_iter(self) -> Self::IntoIter {
		delegate!(self.into_iter())
	}
}

impl<'a, T: Clone, const N: usize, A: Allocator + Clone, const ATOMIC: bool> IntoIterator for &'a mut Unique<'_, T, N, A, ATOMIC> {
	type Item = &'a mut T;
	type IntoIter = IterMut<'a, T>;

	fn into_iter(self) -> Self::IntoIter {
		self.as_mut_slice().iter_mut()
	}
}

impl<T, const N: usize, A: Allocator, const ATOMIC: bool> Extend<T> for Unique<'_, T, N, A, ATOMIC> {
	fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
		if let Err(_) = delegate!(self.try_extend(iter) -> extend_iter) {
			todo!("capacity panic")
		}
	}

	#[cfg(feature = "unstable-traits")]
	#[track_caller]
	fn extend_one(&mut self, item: T) {
		let Ok(()) = self.push(item) else {
			todo!("capacity panic")
		};
	}

	#[cfg(feature = "unstable-traits")]
	fn extend_reserve(&mut self, additional: usize) { }
}

impl<'a, T: Copy + 'a, const N: usize, A: Allocator, const ATOMIC: bool> Extend<&'a T> for Unique<'_, T, N, A, ATOMIC> {
	fn extend<I: IntoIterator<Item = &'a T>>(&mut self, iter: I) {
		if let Err(_) = delegate!(self.try_extend_ref(iter) -> extend_iter) {
			todo!("capacity panic")
		}
	}

	#[cfg(feature = "unstable-traits")]
	#[track_caller]
	fn extend_one(&mut self, item: &'a T) {
		self.extend_one(*item);
	}

	#[cfg(feature = "unstable-traits")]
	fn extend_reserve(&mut self, additional: usize) { }
}

impl<T: Eq, const N: usize, A: Allocator, const ATOMIC: bool> Eq for Unique<'_, T, N, A, ATOMIC> { }

impl<T, const N1: usize, const N2: usize, A1, A2, const ATOMIC1: bool, const ATOMIC2: bool> PartialOrd<Unique<'_, T, N2, A2, ATOMIC2>> for Unique<'_, T, N1, A1, ATOMIC1>
where
	T: PartialOrd,
	A1: Allocator,
	A2: Allocator
{
	fn partial_cmp(&self, other: &Unique<'_, T, N2, A2, ATOMIC2>) -> Option<Ordering> {
		PartialOrd::partial_cmp(self.as_inner(), other.as_inner())
	}
}

impl<T: Ord, const N: usize, A: Allocator, const ATOMIC: bool> Ord for Unique<'_, T, N, A, ATOMIC> {
	fn cmp(&self, other: &Self) -> Ordering {
		Ord::cmp(self.as_inner(), other.as_inner())
	}
}

impl<T: fmt::Debug, const N: usize, A: Allocator, const ATOMIC: bool> fmt::Debug for Unique<'_, T, N, A, ATOMIC> {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		fmt::Debug::fmt(self.as_inner(), f)
	}
}

impl<T, const N: usize, A: Allocator, const ATOMIC: bool> AsRef<Self> for Unique<'_, T, N, A, ATOMIC> {
	fn as_ref(&self) -> &Self { self }
}

impl<T, const N: usize, A: Allocator, const ATOMIC: bool> AsMut<Self> for Unique<'_, T, N, A, ATOMIC> {
	fn as_mut(&mut self) -> &mut Self { self }
}

impl<T, const N: usize, A: Allocator, const ATOMIC: bool> AsRef<[T]> for Unique<'_, T, N, A, ATOMIC> {
	fn as_ref(&self) -> &[T] { self }
}

impl<T, const N: usize, A: Allocator, const ATOMIC: bool> AsMut<[T]> for Unique<'_, T, N, A, ATOMIC> {
	fn as_mut(&mut self) -> &mut [T] { self }
}
