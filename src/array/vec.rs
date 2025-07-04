// Copyright 2025 - Strixpyrr
// SPDX-License-Identifier: Apache-2.0

//! # Internal Layout
//! 
//! The layout of the inner allocation is exactly equivalent to `Rc<(usize, [T; N])>`, three `usize`
//! words plus the array:
//! 
//! ```text
//!  0        8       16       24..
//! |--------|--------|--------|-------~
//! | strong |  weak  | length | array..
//! |--------|--------|--------|-------~
//! ```

use alloc::{boxed::Box, string::String, vec, vec::Vec as StdVec};
use alloc::alloc::Global;
use core::alloc::{AllocError, Allocator};
use core::cmp::Ordering;
use core::{fmt, iter, mem, ptr, slice};
use core::hash::{Hash, Hasher};
use core::mem::{take, ManuallyDrop, MaybeUninit};
use core::ops::{Deref, Index, Range, RangeBounds};
use core::ptr::NonNull;
use core::slice::{ChunksExactMut, ChunksMut, Iter, IterMut, RChunksExactMut, RChunksMut, RSplitMut, RSplitNMut, SliceIndex, SplitInclusiveMut, SplitMut, SplitNMut};
use crate::array::{FullCapacity, TryExtend, TryExtendIter, TryFromSlice, TryInsert};
use crate::error::{Result, Shared};
use crate::marker::RcVector;
#[cfg(feature = "vec")]
use crate::vec::Vec;
pub(crate) use __private::ArrayVec;
use drain::Drain;
use into_iter::IntoIter;
use unique::Unique;
use weak::Weak;
use crate::array::vec::internal::{Copied, CopiedIter};
use crate::raw::{check_size, InnerBase, RawVec, VecInner};

#[cfg(target_has_atomic = "ptr")]
pub mod arc;
pub mod rc;

pub(crate) mod drain;
mod eq;
pub(crate) mod into_iter;
pub(crate) mod unique;
pub(crate) mod weak;
mod internal;

// Workaround for "struct is private" error
mod __private {
	use alloc::alloc::Global;
	use core::alloc::Allocator;
	use core::marker::PhantomData;
	use crate::raw::RawVec;

	pub struct ArrayVec<T, const N: usize, const ATOMIC: bool = false, A: Allocator = Global> {
		pub(crate) inner: RawVec<[T; N], A>,
		pub(crate) len: usize,
	}
}

impl<T, const N: usize, const ATOMIC: bool> ArrayVec<T, N, ATOMIC> {
	/// Creates a new, empty vector with a fixed capacity.
	///
	/// If the fixed capacity is `0`, no memory is allocated.
	///
	/// # Panics
	///
	/// Panics if the capacity `N` is greater than [`isize::MAX`] *bytes* minus three [`usize`]
	/// words, or if the allocator reports an allocation failure.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 8> = ArrayVec::new();
	/// ```
	#[must_use]
	pub fn new() -> Self {
		Self { inner: RawVec::new(Global), len: 0 }
	}

	/// Creates a new, empty vector with a fixed capacity.
	///
	/// If the fixed capacity is `0`, no memory is allocated.
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 8> = ArrayVec::try_new()?;
	/// # Ok::<_, core::alloc::AllocError>(())
	/// ```
	pub fn try_new() -> Result<Self, AllocError> {
		Self::try_new_in(Global)
	}
}

impl<T, const N: usize, A: Allocator, const ATOMIC: bool> ArrayVec<T, N, ATOMIC, A> {
	/// The fixed capacity of the vector.
	pub const CAPACITY: usize = N;

	/// Creates a new, empty vector with a fixed capacity in the given allocator.
	///
	/// # Panics
	///
	/// Panics if the capacity `N` is greater than [`isize::MAX`] minus three [`usize`] words, or if
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 8, _> = ArrayVec::new_in(System);
	/// # }
	/// ```
	#[must_use]
	pub fn new_in(alloc: A) -> Self {
		Self { inner: RawVec::new(alloc), len: 0 }
	}

	/// Creates a new, empty vector with a fixed capacity in the given allocator.
	///
	/// # Errors
	///
	/// Returns an error if the allocator reports an allocation failure.
	///
	/// # Examples
	///
	/// ```
	/// #![feature(allocator_api)]
	/// # #[cfg(feature = "std")]
	/// # {
	/// use std::alloc::System;
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 8, _> = ArrayVec::try_new_in(System)?;
	/// # }
	/// # Ok::<_, core::alloc::AllocError>(())
	/// ```
	pub fn try_new_in(alloc: A) -> Result<Self, AllocError> {
		Ok(Self { inner: RawVec::try_new(alloc)?, len: 0 })
	}
	
	/// Returns the total number of elements the vector can hold.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 8> = ArrayVec::new();
	/// assert_eq!(vec.capacity(), 8);
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 8> = ArrayVec::new();
	/// vec.extend([1, 2, 3]);
	///
	/// assert_eq!(vec.limit(), 5);
	///
	/// vec.extend([0; 5]);
	/// assert_eq!(vec.limit(), 0);
	/// ```
	pub const fn limit(&self) -> usize {
		self.capacity() - self.len()
	}

	/// Returns a slice over the vector contents.
	///
	/// Equivalent to `&s[..]`.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 8> = ArrayVec::new();
	/// vec.try_extend([1, 2, 3]).unwrap();
	///
	/// assert_eq!(vec.as_slice(), [1, 2, 3]);
	/// ```
	pub fn as_slice(&self) -> &[T] {
		// Safety: elements within `len` are valid.
		unsafe {
			self.inner.as_slice(self.len())
		}
	}

	/// Returns a mutable slice over the vector contents, if the vector holds a unique reference.
	///
	/// # Errors
	///
	/// Returns an error if the vector is not empty and holds a shared reference to its buffer. If
	/// the vector is empty, an empty slice is always returned.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 8> = ArrayVec::from([1, 2, 3, 4, 5, 6, 7, 8]);
	/// vec.try_as_mut_slice().unwrap().rotate_left(3);
	///
	/// assert_eq!(vec.as_slice(), [4, 5, 6, 7, 8, 1, 2, 3]);
	/// ```
	pub fn try_as_mut_slice(&mut self) -> Result<&mut [T]> {
		self.check_mutable()?;

		// Safety: the reference is checked to be unique or empty. There is no way for shared memory
		//  to be modified here. Elements within `len` are valid.
		unsafe {
			Ok(self.inner.as_mut_slice(self.len()))
		}
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
	/// [`as_mut_ptr`]: Self::as_mut_ptr
	/// [`as_ptr`]: Self::as_ptr
	/// [`as_non_null`]: Self::as_non_null
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let vec: ArrayVec<i32, 3> = ArrayVec::from([1, 2, 4]);
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 3> = ArrayVec::from([1, 2, 3]);
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
		self.inner.ptr().as_ptr()
	}
	/// Returns a raw pointer to the vector's buffer.
	///
	/// The caller must ensure that the vector outlives the pointer this function returns, or else
	/// it will end up dangling.
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 8> = ArrayVec::new();
	/// let ptr = vec.as_mut_ptr();
	///
	/// // Initialize elements via raw pointer writes, then set length.
	/// // This is safe because no other strong reference points to the vector contents.
	/// unsafe {
	///     for i in 0..vec.capacity() {
	///         ptr.add(i).write(i as i32);
	///     }
	///     vec.set_len(8);
	/// }
	/// assert_eq!(vec, [0, 1, 2, 3, 4, 5, 6, 7]);
	/// ```
	///
	/// Due to the aliasing guarantee, this code is valid:
	///
	/// ```
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 1> = ArrayVec::from([0]);
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
		self.as_non_null().as_ptr()
	}
	/// Returns a `NonNull` pointer to the vector's buffer.
	///
	/// The caller must ensure that the vector outlives the pointer this function returns, or else
	/// will end up dangling.
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 8> = ArrayVec::new();
	/// let ptr = vec.as_non_null();
	///
	/// // Initialize elements via raw pointer writes, then set length.
	/// // This is safe because no other strong reference points to the vector contents.
	/// unsafe {
	///     for i in 0..vec.capacity() {
	///         ptr.add(i).write(i as i32);
	///     }
	///     vec.set_len(8);
	/// }
	/// assert_eq!(vec, [0, 1, 2, 3, 4, 5, 6, 7]);
	/// ```
	///
	/// Due to the aliasing guarantee, this code is valid:
	///
	/// ```
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 1> = ArrayVec::from([0]);
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
		self.inner.ptr()
	}

	/// Returns a reference to the underlying allocator.
	pub const fn allocator(&self) -> &A {
		self.inner.allocator()
	}

	/// Returns `true` if this vector holds the only strong reference to its allocated capacity,
	/// meaning no other vector shares it, allowing modification.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let vec: ArrayVec<i32, 8> = ArrayVec::new();
	/// let weak = vec.demote();
	/// assert!(vec.is_unique());
	/// ```
	pub fn is_unique(&self) -> bool {
		self.strong_count() == 1
	}
	/// Returns `true` if this vector does not hold the only reference to its allocated capacity,
	/// making it read-only. Only strong references count toward sharing.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let vec: ArrayVec<i32, 8> = ArrayVec::new();
	/// let clone = vec.clone();
	/// assert!(vec.is_shared());
	/// ```
	pub fn is_shared(&self) -> bool {
		!self.is_unique()
	}
	/// Returns `true` if this vector's allocated capacity is *not* weakly referenced.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let vec: ArrayVec<i32, 8> = ArrayVec::new();
	/// assert!(vec.is_weakly_unique());
	/// ```
	pub fn is_weakly_unique(&self) -> bool {
		self.weak_count() == 0
	}
	/// Returns `true` if this vector's allocated capacity is weakly referenced.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let vec: ArrayVec<i32, 8> = ArrayVec::new();
	/// let weak = vec.demote();
	/// assert!(vec.is_weakly_shared());
	/// ```
	pub fn is_weakly_shared(&self) -> bool {
		!self.is_weakly_unique()
	}
	
	/// Returns the number of strong references to the vector's allocated capacity.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let vec: ArrayVec<i32, 8> = ArrayVec::new();
	/// let clone = vec.clone();
	/// assert_eq!(vec.strong_count(), 2);
	/// ```
	pub fn strong_count(&self) -> usize {
		self.inner.strong_count::<ATOMIC>().unwrap_or(1)
	}
	/// Returns the number of weak references to the vector's allocated capacity.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::vec::rc::ArrayVec;
 	///
	/// let vec: ArrayVec<i32, 8> = ArrayVec::new();
	/// let weak = vec.demote();
	/// assert_eq!(vec.weak_count(), 1);
	/// ```
	pub fn weak_count(&self) -> usize {
		self.inner.weak_count::<ATOMIC>().unwrap_or(0)
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 2> = ArrayVec::new();
	///
	/// let mut unique = vec.unique().unwrap();
	/// assert_eq!(unique.push(1), Ok(()));
	/// assert_eq!(unique.push(2), Ok(()));
	/// assert_eq!(unique.push(3), Err(3));
	/// drop(unique);
	///
	/// let clone = vec.clone();
	/// assert!(vec.unique().is_err());
	/// drop(clone);
	/// ```
	pub fn unique(&mut self) -> Result<Unique<T, N, A, ATOMIC>> {
		self.check_unique()?;

		if self.is_weakly_shared() {
			// Safety: elements within `len` are valid. The vector is unique.
			unsafe {
				if let Err(err) = self.inner.copy_out(self.len()) {
					err.handle();
				}
			}
		}

		Ok(Unique { vec: self })
	}
	
	/// Shortens the vector, keeping the first `len` elements and dropping the rest. If `len` is
	/// greater or equal to the vector's current length, this has no effect.
	///
	/// # Examples
	/// 
	/// ```
	/// use sharevec::array::vec::rc::ArrayVec;
	/// 
	/// let mut vec: ArrayVec<i32, 5> = ArrayVec::from([1, 2, 3, 4, 5]);
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
	#[allow(clippy::else_if_without_else)]
	pub fn truncate(&mut self, len: usize) {
		if self.is_unique() {
			if self.len() >= len {
				self.len = len;
				// Safety: the reference is checked to be unique.
				unsafe {
					self.inner.truncate(len);
				}
			}
		} else if self.len() >= len {
			self.len = len;
		}
	}

	/// Clears the vector, removing all values.
	///
	/// # Examples
	/// 
	/// ```
	/// use sharevec::array::vec::rc::ArrayVec;
	/// 
	/// let mut vec: ArrayVec<i32, 3> = ArrayVec::from([1, 2, 3]);
	/// vec.clear();
	/// 
	/// assert_eq!(vec, []);
	/// ```
	pub fn clear(&mut self) {
		self.truncate(0)
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
	/// length to `new_len` must be initialized. This implies that the vector contains a unique
	/// reference, as no elements outside the old length could've been initialized with a shared
	/// reference.
	///
	/// # Examples
	///
	/// See [`spare_capacity_mut`] for an example with safe initialization of capacity elements and
	/// use of this method.
	///
	/// [`spare_capacity_mut`]: Self::spare_capacity_mut
	pub unsafe fn set_len(&mut self, new_len: usize) {
		if self.is_unique() {
			self.inner.set_len(&mut self.len, new_len);
		} else {
			self.len = new_len;
		}
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec = ArrayVec::from(['a', 'b', 'c', 'd']);
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
		self.swap_remove_internal(index, |vec| vec.check_unique())
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec = ArrayVec::from(['a', 'b', 'c']);
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
	/// [`ArrayDeque::try_pop_front`], which is also *O*(1).
	///
	/// [`len`]: Self::len
	/// [`try_swap_remove`]: Self::try_swap_remove
	/// [`ArrayDeque::try_pop_front`]: crate::array::deque::ArrayDeque::try_pop_front
	pub fn try_remove(&mut self, index: usize) -> Result<T> {
		self.remove_internal(index, |vec| vec.check_unique())
	}

	/// Inserts an element at position `index` within the vector, shifting all subsequent elements to
	/// the right.
	///
	/// # Errors
	///
	/// Returns [`TryInsert::Shared`] if the vector has free capacity, but is immutable because it
	/// holds a shared reference to its buffer. If the vector is full, [`TryInsert::FullCapacity`]
	/// is returned and the vector is not modified.
	///
	/// # Panics
	///
	/// Panics if `index` is greater than the vector length.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::TryInsert;
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<char, 4> = ArrayVec::new();
	/// vec.try_extend(['a', 'c']).unwrap();
	///
	/// assert_eq!(vec.try_insert(1, 'b'), Ok(()));
	/// assert_eq!(vec, ['a', 'b', 'c']);
	/// assert_eq!(vec.try_insert(3, 'd'), Ok(()));
	/// assert_eq!(vec, ['a', 'b', 'c', 'd']);
	/// assert_eq!(vec.try_insert(0, 'e'), Err(TryInsert::FullCapacity { element: 'e' }));
	/// ```
	///
	/// # Time complexity
	///
	/// Takes at most *O*(*n*) time, as all elements after `index` must be shifted. In the worst
	/// case, all [`len`] elements must be shifted when `index` is `0`.
	///
	/// [`len`]: Self::len
	pub fn try_insert(&mut self, index: usize, element: T) -> Result<(), TryInsert<T>> {
		self.insert_internal(
			index,
			element,
			|element| TryInsert::FullCapacity { element },
			|vec, element| if vec.is_unique() {
				Ok(element)
			} else {
				Err(TryInsert::Shared { element })
			}
		)
	}

	/// Retains the elements specified by `predicate`, dropping the rest.
	///
	/// Removes all elements `e` for which `predicate(&e)` returns `false`. This method operates
	/// in-place, visiting each element exactly once in the original order, and preserves the order
	/// of the retained elements.
	///
	/// # Errors
	///
	/// Returns an error if this operation would shift elements (creating "holes"), but the vector
	/// is immutable because it holds a shared reference to its buffer.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 4> = ArrayVec::from([1, 2, 3, 4]);
	/// assert_eq!(vec.try_retain(|&x| x % 2 == 0), Ok(()));
	/// assert_eq!(vec, [2, 4]);
	/// ```
	pub fn try_retain<F: FnMut(&T) -> bool>(&mut self, predicate: F) -> Result {
		self.retain_checked(predicate)
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 4> = ArrayVec::from([1, 2, 3, 4]);
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
		self.check_mutable()?;

		// Safety: `check_unique` ensures the vector holds a unique reference.
		unsafe {
			self.inner.retain_mutable(&mut self.len, predicate);
		}
		Ok(())
	}

	/// Removes consecutive repeated elements from the vector according to the [`PartialEq`] trait
	/// implementation. If the vector is sorted, all duplicates are removed.
	/// 
	/// This operation requires the vector to hold a unique reference if duplicates are found in the
	/// middle of the vector. If the only duplicates found are at the end, the vector is truncated.
	///
	/// # Errors
	///
	/// Returns an error if the vector contains duplicates which cannot be removed because it holds
	/// a shared reference to its buffer.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 5> = ArrayVec::from([1, 2, 2, 3, 2]);
	/// assert_eq!(vec.try_dedup(), Ok(()));
	/// assert_eq!(vec, [1, 2, 3, 2]);
	/// ```
	pub fn try_dedup(&mut self) -> Result
	where T: PartialEq {
		if self.len() < 2 {
			Ok(())
		} else if self.is_unique() {
			// Safety: `is_unique` ensures the vector holds a unique reference.
			unsafe {
				self.inner.dedup_by_mutable(&mut self.len, |a, b| a == b);
			}
			Ok(())
		} else {
			self.inner.dedup_by_shared(&mut self.len, PartialEq::eq)
		}
	}
	/// Removes consecutive repeated elements from the vector that resolve to the same key given by
	/// `key`. If the vector is sorted, all duplicates are removed.
	///
	/// # Errors
	///
	/// Returns an error if the vector contains more than one element, but is immutable because it
	/// holds a shared reference to its buffer.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 5> = ArrayVec::from([10, 20, 21, 30, 20]);
	/// assert_eq!(vec.try_dedup_by_key(|&mut x| x / 10), Ok(()));
	/// assert_eq!(vec, [10, 20, 30, 20]);
	/// ```
	pub fn try_dedup_by_key<F: FnMut(&mut T) -> K, K: PartialEq>(&mut self, mut key: F) -> Result {
		if self.len() < 2 {
			return Ok(())
		}

		self.check_unique()?;

		// Safety: `check_unique` ensures the vector holds a unique reference.
		unsafe {
			self.inner.dedup_by_mutable(&mut self.len, |a, b| key(a) == key(b));
		}
		Ok(())
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
	/// Returns an error if the vector contains more than one element, but is immutable because it
	/// holds a shared reference to its buffer.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<char, 6> = ArrayVec::from(['a', 'A', 'b', 'c', 'c', 'B']);
	/// assert_eq!(vec.try_dedup_by(|a, b| a.eq_ignore_ascii_case(b)), Ok(()));
	/// assert_eq!(vec, ['a', 'b', 'c', 'B']);
	/// ```
	pub fn try_dedup_by<F: FnMut(&mut T, &mut T) -> bool>(&mut self, predicate: F) -> Result {
		if self.len() < 2 {
			return Ok(())
		}

		self.check_unique()?;

		// Safety: `check_unique` ensures the vector holds a unique reference.
		unsafe {
			self.inner.dedup_by_mutable(&mut self.len, predicate);
		}
		Ok(())
	}

	/// Appends an element to the end of the vector if there is sufficient spare capacity, otherwise
	/// returns an error containing the element.
	///
	/// # Errors
	///
	/// Returns [`TryInsert::Shared`] if the vector is immutable because it holds a shared reference
	/// to its buffer. If the vector is full, [`TryInsert::FullCapacity`] is returned and the vector
	/// is not modified.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::TryInsert;
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 2> = ArrayVec::new();
	/// assert_eq!(vec.try_push(1), Ok(()));
	/// assert_eq!(vec.try_push(2), Ok(()));
	/// assert_eq!(vec.try_push(3), Err(TryInsert::FullCapacity { element: 3 }));
	/// ```
	///
	/// # Time complexity
	///
	/// Takes *O*(1) time.
	pub fn try_push(&mut self, value: T) -> Result<(), TryInsert<T>> {
		if self.is_full() {
			return Err(TryInsert::FullCapacity { element: value })
		}

		if self.is_shared() {
			return Err(TryInsert::Shared { element: value })
		}

		// Safety: `check_unique` ensures the vector holds a unique reference, and the vector is not
		//  full.
		unsafe {
			self.inner.push_unchecked(&mut self.len, value);
		}
		Ok(())
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 2> = ArrayVec::from([1, 2]);
	/// assert_eq!(vec.try_pop(), Ok(Some(2)));
	/// assert_eq!(vec.try_pop(), Ok(Some(1)));
	/// assert_eq!(vec.try_pop(), Ok(None));
	/// ```
	///
	/// # Time complexity
	///
	/// Takes *O*(1) time.
	pub fn try_pop(&mut self) -> Result<Option<T>> {
		if self.is_empty() {
			return Ok(None)
		}

		self.check_unique()?;

		// Safety: `check_unique` ensures the vector holds a unique reference, and the vector is not
		//  empty.
		unsafe {
			Ok(Some(self.inner.pop_unchecked(&mut self.len)))
		}
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 4> = ArrayVec::from([1, 2, 3, 4]);
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
		if self.is_empty() {
			return Ok(None)
		}

		let Some(value) = self.try_last_mut()? else {
			// Emptiness is checked above.
			unreachable!()
		};

		Ok(predicate(value).then(||
			// Safety: `check_unique` ensures the vector holds a unique reference, and the vector is
			//  not empty.
			unsafe {
				self.inner.pop_unchecked(&mut self.len)
			}
		))
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
	/// Returns [`Shared`] if either of the vectors are immutable because they hold a shared
	/// reference to their respective buffers. Returns [`FullCapacity`] if the vector would overflow
	/// its fixed capacity after appending `other`. In either case, neither vector is modified.
	/// 
	/// [`Shared`]: TryExtend::Shared
	/// [`FullCapacity`]: TryExtend::FullCapacity
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::TryExtend;
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec1: ArrayVec<i32, 7> = ArrayVec::new();
	/// vec1.extend([1, 2, 3]);
	/// let mut vec2 = ArrayVec::from([4, 5, 6]);
	/// let mut vec3 = ArrayVec::from([7, 8, 9]);
	/// assert_eq!(vec1.try_append(&mut vec2), Ok(()));
	/// assert_eq!(vec1, [1, 2, 3, 4, 5, 6]);
	/// assert_eq!(vec2, []);
	///
	/// assert_eq!(vec1.try_append(&mut vec3), Err(TryExtend::FullCapacity { remaining: 2 }));
	/// // Vectors are unmodified
	/// assert_eq!(vec1, [1, 2, 3, 4, 5, 6]);
	/// assert_eq!(vec3, [7, 8, 9]);
	/// ```
	pub fn try_append<V: RcVector<T, A, ATOMIC> + ?Sized>(&mut self, other: &mut V) -> Result<(), TryExtend> {
		if other.is_empty() {
			return Ok(())
		}

		if let Some(remaining) = other.len().checked_sub(self.limit()) {
			return Err(TryExtend::FullCapacity { remaining })
		}

		self.check_unique()?;
		if other.is_shared() {
			return Err(TryExtend::Shared)
		}

		// Safety: both vectors are unique. All elements up to `len` in `other`
		//  are valid. `other` is checked not to overflow the capacity.
		unsafe {
			self.inner.append_unique(&mut self.len, other);
		}
		Ok(())
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
	/// Returns an error if `range` is not empty but vector is immutable because it holds a shared
	/// reference to its buffer. If `range` is empty, an empty iterator is always returned.
	///
	/// # Leaking
	///
	/// If the returned iterator goes out of scope without being dropped (due to [`forget`], for
	/// example), the vector may have lost and leaked elements arbitrarily, including elements
	/// outside the range.
	///
	/// [`forget`]: mem::forget
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 8> = ArrayVec::from([1, 2, 3, 4, 5, 6, 7, 8]);
	/// let removed = vec.try_drain(2..6).map(Iterator::collect::<ArrayVec<_, 4>>);
	/// assert_eq!(removed, Ok([3, 4, 5, 6].into()));
	/// assert_eq!(vec, [1, 2, 7, 8]);
	/// ```
	#[allow(clippy::multiple_unsafe_ops_per_block)]
	pub fn try_drain<R: RangeBounds<usize>>(&mut self, range: R) -> Result<Drain<T, N, A, ATOMIC>> {
		let len = self.len();
		let mut range = slice::range(range, ..len);
		
		if !range.is_empty() {
			self.check_unique()?;
		} else {
			// The range is empty, and the vector may be shared. Shift the range to
			// the end to avoid modifying anything, even the length.
			range = len..len;
		}

		// Safety: `slice::range` ensures the range is in-bounds, and the vector is unique.
		unsafe {
			self.set_len(range.start);
			let slice = slice::from_raw_parts(self.as_ptr().add(range.start), range.len());
			let tail = range.end..len;
			Ok(Drain::unique(tail, slice.iter(), self))
		}
	}

	/// Returns the number of elements in the vector.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let vec = ArrayVec::from([1, 2, 3]);
	/// assert_eq!(vec.len(), 3);
	/// ```
	pub const fn len(&self) -> usize { self.len }
	/// Returns `true` if the vector contains no elements.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 1> = ArrayVec::new();
	/// assert!(vec.is_empty());
	///
	/// _ = vec.push(1);
	/// assert!(!vec.is_empty());
	/// ```
	pub const fn is_empty(&self) -> bool {
		self.len() == 0
	}
	/// Returns `true` if the vector contains any elements.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 1> = ArrayVec::new();
	/// assert!(!vec.is_not_empty());
	///
	/// _ = vec.push(1);
	/// assert!(vec.is_not_empty());
	/// ```
	pub const fn is_not_empty(&self) -> bool {
		!self.is_empty()
	}
	/// Returns `true` if the vector cannot hold any more elements.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec = ArrayVec::from([1, 2, 3]);
	/// assert!(vec.is_full());
	///
	/// _ = vec.pop();
	/// assert!(!vec.is_full());
	/// ```
	pub const fn is_full(&self) -> bool {
		self.len() == self.capacity()
	}
	/// Returns `true` if the vector can hold more elements.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec = ArrayVec::from([1, 2, 3]);
	/// assert!(!vec.is_not_full());
	///
	/// _ = vec.pop();
	/// assert!(vec.is_not_full());
	/// ```
	pub const fn is_not_full(&self) -> bool {
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec = ArrayVec::from([1, 2, 3, 4]);
	/// assert!(vec.try_split_off(2).is_ok_and(|v| v == [3, 4]));
	/// assert_eq!(vec, [1, 2]);
	/// ```
	pub fn try_split_off(&mut self, at: usize) -> Result<Self> where A: Clone {
		#[allow(clippy::panic)]
		#[cold]
		#[inline(never)]
		#[track_caller]
		fn assert_failed(at: usize, len: usize) -> ! {
			panic!("`at` split index (is {at}) should be <= len (is {len})");
		}

		let len = self.len();

		if at > len {
			assert_failed(at, len);
		}

		let alloc = self.allocator().clone();
		let drain = self.try_drain(at..len)?;
		let mut split = Self::new_in(alloc);
		// Safety: a newly created vector always holds a unique reference. Drain, by definition,
		//  cannot overflow the capacity.
		unsafe {
			split.inner.extend_trusted(&mut split.len, drain);
		}
		Ok(split)
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
	/// Returns [`Shared`] if the vector is immutable because it holds a shared reference to its
	/// buffer. Returns [`FullCapacity`] if the new length would be larger than the fixed capacity
	/// of the vector. In this case, the vector is filled completely.
	/// 
	/// [`Shared`]: TryExtend::Shared
	/// [`FullCapacity`]: TryExtend::FullCapacity
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::TryExtend;
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 8> = ArrayVec::new();
	/// vec.try_extend([1, 2, 3]).unwrap();
	/// let fill = Default::default;
	///
	/// assert_eq!(vec.try_resize_with(5, fill), Ok(()));
	/// assert_eq!(vec, [1, 2, 3, 0, 0]);
	/// assert_eq!(vec.try_resize_with(3, fill), Ok(()));
	/// assert_eq!(vec, [1, 2, 3]);
	/// assert_eq!(vec.try_resize_with(16, fill), Err(TryExtend::FullCapacity { remaining: 8 }));
	/// assert_eq!(vec, [1, 2, 3, 0, 0, 0, 0, 0]);
	/// ```
	pub fn try_resize_with<F: FnMut() -> T>(&mut self, new_len: usize, fill: F) -> Result<(), TryExtend> {
		let len = self.len();
		if new_len > len {
			if self.is_full() {
				return Err(TryExtend::FullCapacity { remaining: new_len - len })
			}

			self.check_unique()?;
			let fill_len = new_len.min(N) - len;
			// Safety: `check_unique` ensures the vector holds a unique reference, and
			//  `fill_len` will always fit in the vector.
			unsafe {
				self.inner.extend_with(&mut self.len, fill_len, fill);
			}

			if new_len > N {
				Err(TryExtend::FullCapacity { remaining: new_len - N })
			} else {
				Ok(())
			}
		} else {
			self.truncate(new_len);
			Ok(())
		}
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 10> = ArrayVec::new();
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
		if self.is_not_full() {
			self.check_unique()?;
		} 

		// Safety: the check above ensures the vector holds a unique reference if it is not full. If
		//  it is full, this slice will be empty and cannot be modified anyway.
		Ok(unsafe {
			self.inner.as_uninit_slice(self.len())
		})
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
	/// # #![cfg(feature = "unstable-traits")]
	/// use sharevec::array::vec::rc::ArrayVec;
	/// 
	/// let mut vec: ArrayVec<i32, 3> = ArrayVec::from([1, 2, 3]);
	///
	/// for i in 0..vec.len() {
	///     *vec.try_index_mut(i).unwrap() *= 2;
	/// }
	/// assert_eq!(vec, [2, 4, 6]);
	/// 
	/// // `vec.try_index_mut(4)` would panic
	/// ```
	#[cfg(feature = "unstable-traits")]
	pub fn try_index_mut<I: SliceIndex<[T]>>(&mut self, index: I) -> Result<&mut <Self as Index<I>>::Output> {
		self.check_unique()?;

		// Safety: `check_unique` ensures the vector holds a unique reference.
		Ok(unsafe {
			index.index_mut(self.inner.as_mut_slice(self.len()))
		})
	}

	/// Appends elements from an iterator to the vector.
	///
	/// # Errors
	///
	/// Returns [`FullCapacity`] if the vector is filled before the full iterator could be appended.
	/// In this case, the vector is filled completely and the error contains the number of elements
	/// remaining and the partially consumed iterator. [`Shared`] is returned if the vector is
	/// immutable because it holds a shared reference to its buffer.
	///
	/// [`FullCapacity`]: TryExtendIter::FullCapacity
	/// [`Shared`]: TryExtendIter::Shared
	///
	/// # Examples
	/// 
	/// ```
	/// use sharevec::array::vec::rc::ArrayVec;
	/// 
	/// let mut vec: ArrayVec<i32, 3> = ArrayVec::new();
	/// assert_eq!(vec.try_extend([1, 2]), Ok(()));
	/// assert_eq!(vec, [1, 2]);
	/// assert!(vec.try_extend([3, 4, 5]).is_err());
	/// assert_eq!(vec, [1, 2, 3]);
	/// ```
	pub fn try_extend<I: IntoIterator<Item = T>>(&mut self, iter: I) -> Result<(), TryExtendIter<I>> {
		if self.is_full() {
			return Err(TryExtendIter::FullCapacity { first: None, iter: iter.into_iter() })
		}

		if self.is_shared() {
			return Err(TryExtendIter::Shared { iter })
		}

		let mut iter = iter.into_iter();
		for v in iter.by_ref() {
			if self.is_full() {
				return Err(TryExtendIter::FullCapacity {
					first: Some(v),
					iter
				})
			}
			
			// Safety: the vector is checked to be unique and not full.
			unsafe {
				self.inner.push_unchecked(&mut self.len, v);
			}
		}
		
		Ok(())
	}
	/// Appends referenced elements from an iterator to the vector by copying.
	///
	/// # Errors
	///
	///
	/// Returns [`FullCapacity`] if the vector is filled before the full iterator could be appended.
	/// In this case, the vector is filled completely and the error contains the number of elements
	/// remaining and the partially consumed iterator. [`Shared`] is returned if the vector is
	/// immutable because it holds a shared reference to its buffer.
	///
	/// [`FullCapacity`]: TryExtendIter::FullCapacity
	/// [`Shared`]: TryExtendIter::Shared
	///
	/// # Examples
	/// 
	/// ```
	/// use sharevec::array::vec::rc::ArrayVec;
	/// 
	/// let mut vec: ArrayVec<i32, 3> = ArrayVec::new();
	/// assert_eq!(vec.try_extend_ref(&[1, 2]), Ok(()));
	/// assert_eq!(vec, [1, 2]);
	/// assert!(vec.try_extend_ref(&[3, 4, 5]).is_err());
	/// assert_eq!(vec, [1, 2, 3]);
	/// ```
	pub fn try_extend_ref<'a, I: IntoIterator<Item = &'a T>>(&mut self, iter: I) -> Result<(), TryExtendIter<I>>
	where T: Copy + 'a {
		if self.is_full() {
			return Err(TryExtendIter::FullCapacity { first: None, iter: iter.into_iter() })
		}

		if self.is_shared() {
			return Err(TryExtendIter::Shared { iter })
		}

		let mut iter = iter.into_iter();
		for v in iter.by_ref() {
			if self.is_full() {
				return Err(TryExtendIter::FullCapacity {
					first: Some(v),
					iter
				})
			}

			// Safety: the vector is checked to be unique and not full.
			unsafe {
				self.inner.push_unchecked(&mut self.len, *v);
			}
		}

		Ok(())
	}
	
	/// Consumes the vector, returning an iterator over its contents.
	/// 
	/// # Errors
	/// 
	/// Returns the vector back as an error if the vector holds a shared reference to its buffer.
	///
	/// # Examples
	/// 
	/// ```
	/// use sharevec::array::vec::rc::ArrayVec;
	/// 
	/// let mut vec: ArrayVec<i32, 3> = ArrayVec::from([1, 2, 3]);
	/// let mut iter = vec.try_into_iter().unwrap();
	/// assert!(iter.eq([1, 2, 3]));
	/// ```
	pub fn try_into_iter(self) -> Result<IntoIter<T, N, A, ATOMIC>, Self> {
		if self.is_unique() {
			Ok(IntoIter::new_owned(self))
		} else {
			Err(self)
		}
	}
	
	/// Converts the fixed-capacity vector into a variable-capacity vector of capacity `N`.
	///
	/// This may be done even when the vector is shared. This operation takes *O*(1) time, and does
	/// not allocate memory.
	/// 
	/// # Examples
	/// 
	/// ```
	/// use sharevec::array::vec::rc::ArrayVec;
	/// use sharevec::vec::rc::Vec;
	/// 
	/// let array_vec: ArrayVec<i32, 3> = ArrayVec::from([1, 2, 3]);
	/// let mut vec = array_vec.into_vec();
	/// assert_eq!(vec.capacity(), 3);
	/// // The vector can now grow its capacity beyond the initial fixed capacity.
	/// assert_eq!(vec.try_push(4), Ok(()));
	/// ```
	#[cfg(feature = "vec")]
	pub fn into_vec(self) -> Vec<T, ATOMIC, A> {
		let md = ManuallyDrop::new(self);

		// Safety: `inner` is moved out of the vector without dropping.
		let inner = unsafe { ptr::read(&md.inner) };
		Vec { inner: inner.into_slice(), len: md.len }
	}
}

impl<T: Clone, const N: usize, A: Allocator, const ATOMIC: bool> ArrayVec<T, N, ATOMIC, A> {
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
	/// Returns [`Shared`] if the vector is immutable because it holds a shared reference to its
	/// buffer. Returns [`FullCapacity`] if the new length would be larger than the fixed capacity
	/// of the vector. In this case, the vector is filled completely.
	/// 
	/// [`Shared`]: TryExtend::Shared
	/// [`FullCapacity`]: TryExtend::FullCapacity
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::TryExtend;
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 8> = ArrayVec::new();
	/// vec.try_extend([1, 2, 3]).unwrap();
	///
	/// assert_eq!(vec.try_resize(5, 0), Ok(()));
	/// assert_eq!(vec, [1, 2, 3, 0, 0]);
	/// assert_eq!(vec.try_resize(3, 0), Ok(()));
	/// assert_eq!(vec, [1, 2, 3]);
	/// assert_eq!(vec.try_resize(16, 0), Err(TryExtend::FullCapacity { remaining: 8 }));
	/// assert_eq!(vec, [1, 2, 3, 0, 0, 0, 0, 0]);
	/// ```
	pub fn try_resize(&mut self, new_len: usize, value: T) -> Result<(), TryExtend> {
		let len = self.len();
		if new_len > len {
			if self.is_full() {
				return Err(TryExtend::FullCapacity { remaining: new_len - len })
			}
			
			self.check_unique()?;
			let fill_len = new_len.min(N) - len;
			// Safety: `check_unique` ensures the vector holds a unique reference.
			unsafe {
				self.inner.extend_repeated(&mut self.len, fill_len, value);
			}

			if new_len > N {
				Err(TryExtend::FullCapacity { remaining: new_len - N })
			} else {
				Ok(())
			}
		} else {
			self.truncate(new_len);
			Ok(())
		}
	}

	/// Clones and appends all elements in a slice to the vector.
	///
	/// # Errors
	///
	/// Returns [`FullCapacity`] if the vector is filled before the full slice could be appended. In
	/// this case, the vector is filled completely and the error contains the number of elements
	/// remaining. [`Shared`] is returned if the vector is immutable because it holds a shared
	/// reference to its buffer.
	/// 
	/// [`FullCapacity`]: TryExtend::FullCapacity
	/// [`Shared`]: TryExtend::Shared
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::TryExtend;
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 4> = ArrayVec::new();
	/// assert_eq!(vec.try_extend_from_slice(&[1, 2, 3]), Ok(()));
	/// assert_eq!(vec.try_extend_from_slice(&[4, 5, 6]), Err(TryExtend::FullCapacity { remaining: 2 }));
	/// assert_eq!(vec, [1, 2, 3, 4]);
	/// ```
	pub fn try_extend_from_slice(&mut self, other: &[T]) -> Result<(), TryExtend> {
		if other.is_empty() {
			return Ok(())
		}

		if self.is_full() {
			return Err(TryExtend::FullCapacity { remaining: other.len() })
		}

		self.check_unique()?;

		let len = self.limit().min(other.len());
		let remaining = other.len() - len;

		// Safety: `check_unique` ensures the vector holds a unique reference. The length is checked
		//  to not overflow the capacity.
		unsafe {
			self.inner.extend_from_slice(&mut self.len, (&other[..len]).into());
		}

		if remaining > 0 {
			Err(TryExtend::FullCapacity { remaining })
		} else {
			Ok(())
		}
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
	/// Returns [`FullCapacity`] if the vector is filled before the full range could be appended. In
	/// this case, the vector is filled completely and the error contains the number of elements
	/// remaining. [`Shared`] is returned if the vector is immutable because it holds a shared
	/// reference to its buffer.
	/// 
	/// [`FullCapacity`]: TryExtend::FullCapacity
	/// [`Shared`]: TryExtend::Shared
	///
	/// # Examples
	/// 
	/// ```
	/// use sharevec::array::TryExtend;
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 8> = ArrayVec::new();
	/// vec.try_extend([1, 2, 3, 4]).unwrap();
	/// assert_eq!(vec.try_extend_from_within(1..3), Ok(()));
	/// assert_eq!(vec, [1, 2, 3, 4, 2, 3]);
	/// assert_eq!(vec.try_extend_from_within(0..3), Err(TryExtend::FullCapacity { remaining: 1 }));
	/// assert_eq!(vec, [1, 2, 3, 4, 2, 3, 1, 2]);
	/// ```
	pub fn try_extend_from_within<R: RangeBounds<usize>>(&mut self, range: R) -> Result<(), TryExtend> {
		let vec_len = self.len();
		let range = slice::range(range, ..vec_len);

		if range.is_empty() {
			return Ok(())
		}

		if self.is_full() {
			return Err(TryExtend::FullCapacity { remaining: range.len() })
		}

		self.check_unique()?;

		let len = self.limit().min(range.len());
		let remaining = range.len() - len;
		

		// Safety: this range is checked to be in-bounds and not longer than the
		//  available capacity. `check_unique` ensures the vector holds a unique
		//  reference.
		unsafe {
			self.inner.extend_from_within(&mut self.len, range.start..range.start + len);
		}

		if remaining > 0 {
			Err(TryExtend::FullCapacity { remaining })
		} else {
			Ok(())
		}
	}
}

// Mutable slice operations
impl<T, const N: usize, A: Allocator, const ATOMIC: bool> ArrayVec<T, N, ATOMIC, A> {
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 3> = ArrayVec::from([0, 1, 2]);
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 3> = ArrayVec::from([0, 1, 2]);
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 3> = ArrayVec::from([0, 1, 2]);
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 3> = ArrayVec::from([0, 1, 2]);
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 3> = ArrayVec::from([0, 1, 2]);
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 3> = ArrayVec::from([0, 1, 2]);
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 3> = ArrayVec::from([0, 1, 2]);
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 3> = ArrayVec::from([0, 1, 2]);
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 3> = ArrayVec::from([0, 1, 2]);
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

	/// Returns a mutable reference to the underlying array, or `None` if the vector length is not
	/// exactly equal to the fixed capacity `N`.
	///
	/// # Errors
	///
	/// Returns an error if the vector length is equal to the fixed capacity, but the vector holds a
	/// shared reference to its buffer. If the length is less than the fixed capacity, `None` is
	/// always returned.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 3> = ArrayVec::from([0, 1, 2]);
	///
	/// if let Ok(Some(array)) = vec.try_as_mut_array() {
	///     *array = [3, 4, 5];
	/// }
	/// assert_eq!(vec, [3, 4, 5]);
	///
	/// vec.clear();
	/// assert_eq!(vec.try_as_mut_array(), Ok(None));
	/// ```
	pub fn try_as_mut_array(&mut self) -> Result<Option<&mut [T; N]>> {
		if self.is_not_full() {
			Ok(None)
		} else if self.is_shared() {
			Err(Shared(()))
		} else {
			// Safety: this pointer comes from a valid reference, and the length has been checked to
			//  equal `N`.
			Ok(Some(unsafe {
				&mut *self.as_mut_ptr().cast()
			}))
		}
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 5> = ArrayVec::from([1, 2, 3, 4, 5]);
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 3> = ArrayVec::from([1, 2, 3]);
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 3> = ArrayVec::from([1, 2, 4]);
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 5> = ArrayVec::from([0, 0, 0, 0, 0]);
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
	/// # Errors
	///
	/// Returns an error if the vector is not empty and holds a shared reference to its buffer. If
	/// the vector is empty, an empty iterator is always returned.
	///
	/// [`try_chunks_mut`]: Self::try_chunks_mut
	/// [`try_rchunks_exact_mut`]: Self::try_rchunks_exact_mut
	///
	/// # Panics
	///
	/// Panics if `chunk_size` is zero.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 5> = ArrayVec::from([0, 0, 0, 0, 0]);
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 5> = ArrayVec::from([0, 0, 0, 0, 0]);
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 5> = ArrayVec::from([0, 0, 0, 0, 0]);
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 6> = ArrayVec::from([1, 0, 3, 0, 5, 6]);
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 6> = ArrayVec::from([10, 40, 30, 20, 60, 50]);
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 6> = ArrayVec::from([10, 40, 30, 20, 60, 50]);
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 6> = ArrayVec::from([10, 40, 30, 20, 60, 50]);
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 6> = ArrayVec::from([10, 40, 30, 20, 60, 50]);
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 6> = ArrayVec::from([10, 40, 30, 20, 60, 50]);
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<char, 6> = ArrayVec::from(['a', 'b', 'c', 'd', 'e', 'f']);
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<char, 6> = ArrayVec::from(['a', 'b', 'c', 'd', 'e', 'f']);
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 8> = ArrayVec::from([0; 8]);
	/// assert!(vec.try_fill(1).is_ok());
	/// assert_eq!(vec, [1; 8]);
	/// ```
	pub fn try_fill(&mut self, value: T) -> Result
	where
		T: Clone,
	{
		// Don't defer to `<[T]>::fill` because `clone` could panic, cluttering
		// the backtrace. The compiler appears to be smart enough to not need
		// specialization over copy anyway, replacing this loop with `memset`
		// where appropriate.
		for elem in self.try_as_mut_slice()? {
			elem.clone_from(&value);
		}
		
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 8> = ArrayVec::from([1; 8]);
	/// assert!(vec.try_fill_with(Default::default).is_ok());
	/// assert_eq!(vec, [0; 8]);
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
impl<T: Clone, const N: usize, A: Allocator + Clone, const ATOMIC: bool> ArrayVec<T, N, ATOMIC, A> {
	/// Returns a mutable slice over the vector contents, cloning out of a shared allocation.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 3> = ArrayVec::from([1, 2, 3]);
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
		self.make_mutable();

		// Safety: `make_mutable` ensures the vector holds a unique reference, or that it's empty,
		//  in which case no contents will be modified.
		unsafe {
			self.inner.as_mut_slice(self.len())
		}
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 10> = ArrayVec::new();
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
		if self.is_not_full() {
			self.make_unique();
		}

		// Safety: the check above ensures the vector holds a unique reference if it is not full. If
		//  it is full, this slice will be empty and cannot be modified anyway.
		unsafe {
			self.inner.as_uninit_slice(self.len())
		}
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
	/// use sharevec::array::vec::rc::ArrayVec;
	/// 
	/// let mut vec: ArrayVec<i32, 3> = ArrayVec::from([1, 2, 3]);
	/// let clone = vec.clone();
	///
	/// let mut unique = vec.as_unique();
	/// unique.clear();
	/// unique.extend_from_slice(&[4, 5, 6]).unwrap();
	/// assert!(vec.is_unique());
	/// assert_eq!(vec, [4, 5, 6]);
	///
	/// // The first vector's contents have been cloned and are no longer shared
	/// // with the second.
	/// assert!(clone.is_unique());
	/// assert_ne!(vec, clone);
	/// ```
	pub fn as_unique(&mut self) -> Unique<T, N, A, ATOMIC> {
		self.make_unique();

		if self.is_weakly_shared() {
			// We have a unique vector, but some weak pointers exist which may be promoted while the
			// unique wrapper exists, causing the vector to shared *and* mutable. We need to move
			// the contents into a new vector before returning, but don't need to clone.
			// Safety: the vector has been made unique.
			unsafe {
				if let Err(err) = self.inner.copy_out(self.len()) {
					err.handle();
				}
			}
		}

		Unique { vec: self }
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 3> = ArrayVec::from([1, 2, 3]);
	/// let clone = vec.clone();
	///
	/// let mut unique = vec.try_as_unique().expect("allocation failed");
	/// unique.clear();
	/// unique.extend_from_slice(&[4, 5, 6]).unwrap();
	/// assert!(vec.is_unique());
	/// assert_eq!(vec, [4, 5, 6]);
	///
	/// // The first vector's contents have been cloned and are no longer shared
	/// // with the second.
	/// assert!(clone.is_unique());
	/// assert_ne!(vec, clone);
	/// ```
	pub fn try_as_unique(&mut self) -> Result<Unique<T, N, A, ATOMIC>, AllocError> {
		self.try_make_unique()?;

		if self.is_weakly_shared() {
			// We have a unique vector, but some weak pointers exist which may be promoted while the
			// unique wrapper exists, causing the vector to be shared *and* mutable. We need to move
			// the contents into a new vector before returning, but don't need to clone.
			// Safety: the vector has been made unique.
			unsafe {
				self.inner.copy_out(self.len())?;
			}
		}

		Ok(Unique { vec: self })
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec = ArrayVec::from(['a', 'b', 'c', 'd']);
	///
	/// assert_eq!(vec.swap_remove(1), 'b');
	/// assert_eq!(vec, ['a', 'd', 'c']);
	///
	/// assert_eq!(vec.swap_remove(0), 'a');
	/// assert_eq!(vec, ['c', 'd']);
	/// ```
	pub fn swap_remove(&mut self, index: usize) -> T {
		if self.is_not_empty() && index == self.len() - 1 {
			// Avoid cloning the entire vector for a pop operation.
			// Safety: the vector is not empty.
			return unsafe {
				self.pop().unwrap_unchecked()
			}
		}
		
		let Ok(v) = self.swap_remove_internal(index, |vec| {
			vec.make_unique();
			Ok::<_, ()>(())
		}) else { unreachable!() };
		v
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec = ArrayVec::from(['a', 'b', 'c']);
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
		if self.is_not_empty() && index == self.len() - 1 {
			// Avoid cloning the entire vector for a pop operation.
			// Safety: the vector is not empty.
			return unsafe {
				self.pop().unwrap_unchecked()
			}
		}

		let Ok(v) = self.remove_internal(index, |vec| {
			vec.make_unique();
			Ok::<_, ()>(())
		}) else { unreachable!() };
		v
	}

	/// Inserts an element at position `index` within the vector, shifting all subsequent elements to
	/// the right.
	///
	/// If the vector is shared, its contents will be cloned into a unique allocation. A fallible
	/// version is also provided: [`try_insert`].
	///
	/// [`try_insert`]: Self::try_insert
	///
	/// # Errors
	///
	/// If the vector is full, `element` is returned and the vector is not modified.
	///
	/// # Panics
	///
	/// Panics if `index` is greater than the vector length.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::TryInsert;
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<char, 4> = ArrayVec::new();
	/// vec.extend(['a', 'c']);
	///
	/// assert_eq!(vec.insert(1, 'b'), Ok(()));
	/// assert_eq!(vec, ['a', 'b', 'c']);
	/// assert_eq!(vec.insert(3, 'd'), Ok(()));
	/// assert_eq!(vec, ['a', 'b', 'c', 'd']);
	/// assert_eq!(vec.insert(0, 'e'), Err('e'));
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
	pub fn insert(&mut self, index: usize, element: T) -> Result<(), T> {
		self.insert_internal(index, element, |e| e, |vec, elem| {
			vec.make_unique();
			Ok(elem)
		})
	}

	/// Retains the elements specified by `predicate`, dropping the rest.
	///
	/// Removes all elements `e` for which `predicate(&e)` returns `false`. This method operates
	/// in-place, visiting each element exactly once in the original order, and preserves the order
	/// of the retained elements.
	///
	/// If the vector is shared, its contents will be cloned into a unique allocation if any
	/// modifications are needed. A fallible version is also provided: [`try_retain`].
	///
	/// [`try_retain`]: Self::try_retain
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 4> = ArrayVec::from([1, 2, 3, 4]);
	/// vec.retain(|&x| x % 2 == 0);
	/// assert_eq!(vec, [2, 4]);
	/// ```
	pub fn retain<F: FnMut(&T) -> bool>(&mut self, mut predicate: F) {
		self.retain_internal_clone(|e| predicate(e));
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 4> = ArrayVec::from([1, 2, 3, 4]);
	/// vec.retain_mut(|x| if *x % 2 == 0 {
	///     *x += 1;
	///     true
	/// } else {
	///     false
	/// });
	/// assert_eq!(vec, [3, 5]);
	/// ```
	pub fn retain_mut<F: FnMut(&mut T) -> bool>(&mut self, predicate: F) {
		self.retain_internal_clone(predicate);
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 5> = ArrayVec::from([1, 2, 2, 3, 2]);
	/// vec.dedup();
	/// assert_eq!(vec, [1, 2, 3, 2]);
	/// ```
	#[allow(clippy::else_if_without_else)]
	pub fn dedup(&mut self) where T: PartialEq {
		if self.len < 2 || self.is_unique() {
			// Safety: `is_unique` ensures the vector holds a unique reference
			//  if it would be modified.
			unsafe {
				self.inner.dedup_by_mutable(&mut self.len, |a, b| a == b);
			}
		} else if self.len >= 2 && self.is_shared() {
			todo!("implement `dedup_by_clone`")
		}
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 5> = ArrayVec::from([10, 20, 21, 30, 20]);
	/// vec.dedup_by_key(|&mut x| x / 10);
	/// assert_eq!(vec, [10, 20, 30, 20]);
	/// ```
	#[allow(clippy::else_if_without_else)]
	pub fn dedup_by_key<F: FnMut(&mut T) -> K, K: PartialEq>(&mut self, mut key: F) {
		if self.len < 2 || self.is_unique() {
			// Safety: `is_unique` ensures the vector holds a unique reference
			//  if it would be modified.
			unsafe {
				self.inner.dedup_by_mutable(&mut self.len, |a, b| key(a) == key(b));
			}
		} else if self.len >= 2 && self.is_shared() {
			todo!("implement `dedup_by_clone`")
		}
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<char, 6> = ArrayVec::from(['a', 'A', 'b', 'c', 'c', 'B']);
	/// vec.dedup_by(|a, b| a.eq_ignore_ascii_case(b));
	/// assert_eq!(vec, ['a', 'b', 'c', 'B']);
	/// ```
	#[allow(clippy::else_if_without_else)]
	pub fn dedup_by<F: FnMut(&mut T, &mut T) -> bool>(&mut self, predicate: F) {
		if self.len < 2 || self.is_unique() {
			// Safety: `is_unique` ensures the vector holds a unique reference
			//  if it would be modified.
			unsafe {
				self.inner.dedup_by_mutable(&mut self.len, predicate);
			}
		} else if self.len >= 2 && self.is_shared() {
			todo!("implement `dedup_by_clone`")
		}
	}

	/// Appends an element to the end of the vector if there is sufficient spare capacity, otherwise
	/// returns an error containing the element.
	///
	/// If the vector is shared, its contents will be cloned into a unique allocation. A fallible
	/// version is also provided: [`try_push`].
	///
	/// [`try_push`]: Self::try_push
	///
	/// # Errors
	///
	/// Returns the element if the vector is full.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::TryInsert;
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 2> = ArrayVec::new();
	/// assert_eq!(vec.push(1), Ok(()));
	/// assert_eq!(vec.push(2), Ok(()));
	/// assert_eq!(vec.push(3), Err(3));
	/// ```
	///
	/// # Time complexity
	///
	/// Takes *O*(1) time for unique vectors, *O*(*n*) time for shared vectors.
	pub fn push(&mut self, value: T) -> Result<(), T> {
		if self.is_full() {
			Err(value)
		} else {
			self.make_unique();
			// Safety: `make_unique` ensures the vector holds a unique reference, and the vector is
			//  not full.
			unsafe {
				self.inner.push_unchecked(&mut self.len, value);
			}
			Ok(())
		}
	}

	/// Moves all elements from `other` into the vector, leaving `other` empty. Any like[^atomic]
	/// vector type from this crate may be appended, even array vectors with a different fixed
	/// capacity.
	///
	/// If one vector is shared, its contents are cloned into a unique allocation before proceeding.
	/// If `other` is shared, its contents are cloned into `self`. A fallible version is also
	/// provided: [`try_append`].
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
	/// # Errors
	///
	/// Returns an error if the vector would overflow its fixed capacity after appending `other`. In
	/// this case, neither vector is modified.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::FullCapacity;
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec1: ArrayVec<i32, 7> = ArrayVec::new();
	/// vec1.extend([1, 2, 3]);
	/// let mut vec2 = ArrayVec::from([4, 5, 6]);
	/// let mut vec3 = ArrayVec::from([7, 8, 9]);
	/// assert_eq!(vec1.append(&mut vec2), Ok(()));
	/// assert_eq!(vec1, [1, 2, 3, 4, 5, 6]);
	/// assert_eq!(vec2, []);
	///
	/// assert_eq!(vec1.append(&mut vec3), Err(FullCapacity { remaining: 2 }));
	/// // Vectors are unmodified
	/// assert_eq!(vec1, [1, 2, 3, 4, 5, 6]);
	/// assert_eq!(vec3, [7, 8, 9]);
	/// ```
	pub fn append<V: RcVector<T, A, ATOMIC> + ?Sized>(&mut self, other: &mut V) -> Result<(), FullCapacity> {
		if other.is_empty() {
			return Ok(())
		}

		if let Some(remaining) = other.len().checked_sub(self.limit()) {
			return Err(FullCapacity { remaining })
		}

		self.make_unique();

		if other.is_shared() {
			// Safety: `self` is unique. All elements up to `len` in `other` are
			//  valid. `other` is checked to not overflow the capacity.
			unsafe {
				self.inner.append_shared(&mut self.len, other);
			}
		} else {
			// Safety: both vectors are unique. All elements up to `len` in
			//  `other` are valid. `other` is checked to not overflow the
			//  capacity.
			unsafe {
				self.inner.append_unique(&mut self.len, other);
			}
		}
		
		Ok(())
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
	/// [`forget`]: mem::forget
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 8> = ArrayVec::from([1, 2, 3, 4, 5, 6, 7, 8]);
	/// let removed = vec.drain(2..6);
	/// assert!(removed.eq([3, 4, 5, 6]));
	/// assert_eq!(vec, [1, 2, 7, 8]);
	/// ```
	#[allow(clippy::multiple_unsafe_ops_per_block)]
	pub fn drain<R: RangeBounds<usize>>(&mut self, range: R) -> Drain<T, N, A, ATOMIC> {
		let len = self.len();
		let mut range = slice::range(range, ..len);
		
		if range.is_empty() {
			range = len..len;
		}

		// Safety: elements within the range are valid.
		unsafe {
			self.set_len(range.start);
			let slice = slice::from_raw_parts(self.as_ptr().add(range.start), range.len());
			let tail = range.end..len;
			
			if range.is_empty() || self.is_unique() {
				Drain::unique(tail, slice.iter(), self)
			} else {
				Drain::cloning(tail, slice.iter(), self)
			}
		}
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
	/// [`mem::take`]: take
	/// [`mem::replace`]: mem::replace
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec = ArrayVec::from([1, 2, 3, 4]);
	/// assert_eq!(vec.split_off(2), [3, 4]);
	/// assert_eq!(vec, [1, 2]);
	/// ```
	#[must_use = "use `.truncate()` if you don't need the other half"]
	pub fn split_off(&mut self, at: usize) -> Self {
		#[allow(clippy::panic)]
		#[cold]
		#[inline(never)]
		#[track_caller]
		fn assert_failed(at: usize, len: usize) -> ! {
			panic!("`at` split index (is {at}) should be <= len (is {len})");
		}

		let len = self.len();

		if at > len {
			assert_failed(at, len);
		}

		let alloc = self.allocator().clone();
		let drain = self.drain(at..len);
		let mut split = Self::new_in(alloc);
		// Safety: a newly created vector always holds a unique reference.
		unsafe {
			split.inner.extend_trusted(&mut split.len, drain);
		}
		split
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
	/// # Errors
	/// 
	/// Returns an error if the new length would be larger than the fixed capacity of the vector. In
	/// this case, the vector if filled completely.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::FullCapacity;
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 8> = ArrayVec::new();
	/// vec.extend([1, 2, 3]);
	/// let fill = Default::default;
	///
	/// assert_eq!(vec.resize_with(5, fill), Ok(()));
	/// assert_eq!(vec, [1, 2, 3, 0, 0]);
	/// assert_eq!(vec.resize_with(3, fill), Ok(()));
	/// assert_eq!(vec, [1, 2, 3]);
	/// assert_eq!(vec.resize_with(16, fill), Err(FullCapacity { remaining: 8 }));
	/// assert_eq!(vec, [1, 2, 3, 0, 0, 0, 0, 0]);
	/// ```
	pub fn resize_with<F: FnMut() -> T>(&mut self, new_len: usize, fill: F) -> Result<(), FullCapacity> {
		let len = self.len();
		if new_len > len {
			if self.is_full() {
				return Err(FullCapacity { remaining: new_len - len })
			}
			
			self.make_unique();
			let fill_len = new_len.min(N) - len;
			// Safety: `check_unique` ensures the vector holds a unique reference, and
			//  `fill_len` will always fit in the vector.
			unsafe {
				self.inner.extend_with(&mut self.len, fill_len, fill);
			}

			if new_len > N {
				Err(FullCapacity { remaining: new_len - N })
			} else {
				Ok(())
			}
		} else {
			self.truncate(new_len);
			Ok(())
		}
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
	/// # Errors
	///
	/// Returns an error if the new length would be larger than the fixed capacity of the vector. In
	/// this case, the vector is filled completely.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::FullCapacity;
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 8> = ArrayVec::new();
	/// vec.extend([1, 2, 3]);
	///
	/// assert_eq!(vec.resize(5, 0), Ok(()));
	/// assert_eq!(vec, [1, 2, 3, 0, 0]);
	/// assert_eq!(vec.resize(3, 0), Ok(()));
	/// assert_eq!(vec, [1, 2, 3]);
	/// assert_eq!(vec.resize(16, 0), Err(FullCapacity { remaining: 8 }));
	/// assert_eq!(vec, [1, 2, 3, 0, 0, 0, 0, 0]);
	/// ```
	pub fn resize(&mut self, new_len: usize, value: T) -> Result<(), FullCapacity> {
		let len = self.len();
		if new_len > len {
			if self.is_full() {
				return Err(FullCapacity { remaining: new_len - len })
			}

			self.make_unique();
			let fill_len = new_len.min(N) - len;
			// Safety: `check_unique` ensures the vector holds a unique reference, and
			//  `fill_len` will always fit in the vector.
			unsafe {
				self.inner.extend_repeated(&mut self.len, fill_len, value);
			}

			if new_len > N {
				Err(FullCapacity { remaining: new_len - N })
			} else {
				Ok(())
			}
		} else {
			self.truncate(new_len);
			Ok(())
		}
	}

	/// Clones and appends all elements in a slice to the vector.
	///
	/// If the vector is shared, its contents are cloned into a unique allocation.
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 4> = ArrayVec::new();
	/// assert_eq!(vec.extend_from_slice(&[1, 2, 3]), Ok(()));
	/// assert_eq!(vec.extend_from_slice(&[4, 5, 6]), Err(FullCapacity { remaining: 2 }));
	/// assert_eq!(vec, [1, 2, 3, 4]);
	/// ```
	pub fn extend_from_slice(&mut self, other: &[T]) -> Result<(), FullCapacity> {
		if other.is_empty() {
			return Ok(())
		}

		if self.is_full() {
			return Err(FullCapacity { remaining: other.len() })
		}

		self.make_unique();

		let len = self.limit().min(other.len());
		let remaining = other.len() - len;

		// Safety: `check_unique` ensures the vector holds a unique reference. The length is checked
		//  to not overflow the capacity.
		unsafe {
			self.inner.extend_from_slice(&mut self.len, (&other[..len]).into());
		}

		if remaining > 0 {
			Err(FullCapacity { remaining })
		} else {
			Ok(())
		}
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 8> = ArrayVec::new();
	/// vec.extend([1, 2, 3, 4]);
	/// assert_eq!(vec.extend_from_within(1..3), Ok(()));
	/// assert_eq!(vec, [1, 2, 3, 4, 2, 3]);
	/// assert_eq!(vec.extend_from_within(0..3), Err(FullCapacity { remaining: 1 }));
	/// assert_eq!(vec, [1, 2, 3, 4, 2, 3, 1, 2]);
	/// ```
	pub fn extend_from_within<R: RangeBounds<usize>>(&mut self, range: R) -> Result<(), FullCapacity> {
		let vec_len = self.len();
		let range = slice::range(range, ..vec_len);

		if range.is_empty() {
			return Ok(())
		}

		if self.is_full() {
			return Err(FullCapacity { remaining: range.len() })
		}

		self.make_unique();

		let len = self.limit().min(range.len());
		let remaining = range.len() - len;
		
		// Safety: this range is checked to be in-bounds and not longer than the
		//  available capacity. `check_unique` ensures the vector holds a unique
		//  reference.
		unsafe {
			self.inner.extend_from_within(&mut self.len, range.start..range.start + len);
		}

		if remaining > 0 {
			Err(FullCapacity { remaining })
		} else {
			Ok(())
		}
	}
}

impl<T: Clone, const N: usize, A: Allocator, const ATOMIC: bool> ArrayVec<T, N, ATOMIC, A> {
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 2> = ArrayVec::from([1, 2]);
	/// assert_eq!(vec.pop(), Some(2));
	/// assert_eq!(vec.pop(), Some(1));
	/// assert_eq!(vec.pop(), None);
	/// ```
	pub fn pop(&mut self) -> Option<T> {
		let ptr = self.last()? as *const T;
		// Set the length first, in case `T::clone` panics.
		// Safety: the element is moved out if the vector is unique or cloned if the vector is
		//  shared. All elements within `len` remain valid.
		unsafe {
			self.set_len(self.len() - 1);
		}

		let element = if self.is_unique() {
			// Safety: the element has already been removed from the vector above, so cannot be
			//  aliased.
			unsafe {
				ptr.read()
			}
		} else {
			// Safety: the element is valid, as it was part of the length before truncation and has
			//  not been touched.
			unsafe {
				(*ptr).clone()
			}
		};
		Some(element)
	}

	/// Removes and returns the last element from the vector if the predicate returns `true`, or
	/// `None` if predicate returns `false` or the vector is empty. If the vector is empty, the
	/// predicate is not called.
	/// 
	/// This clones the element out of a shared reference.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 4> = ArrayVec::from([1, 2, 3, 4]);
	/// let even = |x: &mut i32| *x % 2 == 0;
	/// assert_eq!(vec.pop_if(even), Some(4));
	/// assert_eq!(vec, [1, 2, 3]);
	/// assert_eq!(vec.pop_if(even), None);
	/// ```
	///
	/// # Time complexity
	///
	/// Takes *O*(1) time.
	#[allow(clippy::multiple_unsafe_ops_per_block)]
	pub fn pop_if<F: FnOnce(&mut T) -> bool>(&mut self, predicate: F) -> Option<T> {
		if self.is_empty() {
			return None
		}

		let idx = self.len() - 1;
		if self.is_unique() {
			// Safety: elements within the length are valid.
			unsafe {
				let ptr = self.as_mut_ptr().add(idx);

				predicate(&mut *ptr).then(|| {
					let value = ptr.read();
					self.set_len(idx);
					value
				})
			}
		} else {
			let mut value = self[idx].clone();
			predicate(&mut value).then(|| {
				// Safety: elements within the length are valid.
				unsafe {
					self.set_len(idx);
				}
				value
			})
		}
	}
}

// CoW mutable slice operations
impl<T: Clone, const N: usize, A: Allocator + Clone, const ATOMIC: bool> ArrayVec<T, N, ATOMIC, A> {
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 3> = ArrayVec::from([0, 1, 2]);
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 3> = ArrayVec::from([0, 1, 2]);
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 3> = ArrayVec::from([0, 1, 2]);
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 3> = ArrayVec::from([0, 1, 2]);
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 3> = ArrayVec::from([0, 1, 2]);
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 3> = ArrayVec::from([0, 1, 2]);
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 3> = ArrayVec::from([0, 1, 2]);
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 3> = ArrayVec::from([0, 1, 2]);
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 3> = ArrayVec::from([0, 1, 2]);
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

	/// Returns a mutable reference to the underlying array, or `None` if the vector length is not
	/// exactly equal to the fixed capacity `N`.
	///
	/// If the vector holds a shared reference, its contents are cloned into a unique allocation. To
	/// return an error if the vector is shared, without allocating or cloning, use
	/// [`try_as_mut_array`] instead.
	///
	/// [`try_as_mut_array`]: Self::try_as_mut_array
	///
	/// # Panics
	///
	/// Panics if allocation fails, for example in an out-of-memory condition.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 3> = ArrayVec::from([0, 1, 2]);
	///
	/// if let Some(array) = vec.as_mut_array() {
	///     *array = [3, 4, 5];
	/// }
	/// assert_eq!(vec, [3, 4, 5]);
	///
	/// vec.clear();
	/// assert_eq!(vec.as_mut_array(), None);
	/// ```
	pub fn as_mut_array(&mut self) -> Option<&mut [T; N]> {
		self.is_full().then(|| {
			let slice = self.as_mut_slice();
			// Safety: this pointer comes from a valid reference, and the length has been checked to
			//  equal `N`.
			unsafe {
				&mut *self.as_mut_ptr().cast()
			}
		})
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 5> = ArrayVec::from([1, 2, 3, 4, 5]);
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 3> = ArrayVec::from([1, 2, 3]);
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 3> = ArrayVec::from([1, 2, 4]);
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 5> = ArrayVec::from([0, 0, 0, 0, 0]);
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 5> = ArrayVec::from([0, 0, 0, 0, 0]);
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 5> = ArrayVec::from([0, 0, 0, 0, 0]);
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 5> = ArrayVec::from([0, 0, 0, 0, 0]);
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 6> = ArrayVec::from([1, 0, 3, 0, 5, 6]);
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 6> = ArrayVec::from([10, 40, 30, 20, 60, 50]);
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 6> = ArrayVec::from([10, 40, 30, 20, 60, 50]);
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 6> = ArrayVec::from([10, 40, 30, 20, 60, 50]);
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 6> = ArrayVec::from([10, 40, 30, 20, 60, 50]);
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 6> = ArrayVec::from([10, 40, 30, 20, 60, 50]);
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<char, 6> = ArrayVec::from(['a', 'b', 'c', 'd', 'e', 'f']);
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<char, 6> = ArrayVec::from(['a', 'b', 'c', 'd', 'e', 'f']);
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 8> = ArrayVec::from([0; 8]);
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
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let mut vec: ArrayVec<i32, 8> = ArrayVec::from([1; 8]);
	/// vec.fill_with(Default::default);
	/// assert_eq!(vec, [0; 8]);
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
		
		let mut target = Self::new_in(self.allocator().clone());
		
		for _ in 0..self.len {
			// Safety: `target` was just created, so must be unique.
			unsafe {
				target.inner.push_unchecked(&mut target.len, fill());
			}
		}
		
		*self = target;
	}
}

impl<T, const N: usize, A: Allocator, const ATOMIC: bool> Deref for ArrayVec<T, N, ATOMIC, A> {
	type Target = [T];

	fn deref(&self) -> &[T] {
		self.as_slice()
	}
}

impl<T, const N: usize, A: Allocator + Clone, const ATOMIC: bool> Clone for ArrayVec<T, N, ATOMIC, A> {
	/// Creates a new vector sharing its contents with this vector.
	/// 
	/// If the fixed capacity is `0`, both vectors remain unique.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::vec::rc::ArrayVec;
	///
	/// let vec = ArrayVec::from([1, 2, 3]);
	/// let clone = vec.clone();
	///
	/// // Both vectors are now shared.
	/// assert!(vec.is_shared());
	/// assert!(clone.is_shared());
	/// ```
	fn clone(&self) -> Self {
		Self { inner: self.inner.share::<ATOMIC>(), ..*self }
	}
}

impl<T: Hash, const N: usize, A: Allocator, const ATOMIC: bool> Hash for ArrayVec<T, N, ATOMIC, A> {
	fn hash<H: Hasher>(&self, state: &mut H) {
		Hash::hash(&**self, state)
	}
}

impl<T, const N: usize, I: SliceIndex<[T]>, A: Allocator, const ATOMIC: bool> Index<I> for ArrayVec<T, N, ATOMIC, A> {
	type Output = I::Output;

	fn index(&self, index: I) -> &Self::Output {
		Index::index(&**self, index)
	}
}

impl<T, const N: usize, const ATOMIC: bool> FromIterator<T> for ArrayVec<T, N, ATOMIC> {
	/// Creates a new vector for an iterator.
	///
	/// # Panics
	///
	/// Panics if the iterator is yields more than elements than the fixed capacity can hold, or if
	/// allocation fails, for example in an out-of-memory condition.
	#[allow(clippy::panic)]
	fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
		let mut vec = Self::new();
		match vec.try_extend(iter) {
			Ok(()) => vec,
			Err(TryExtendIter::Shared { .. }) =>
				// Safety: a new vector is always unique.
				unsafe {
					core::hint::unreachable_unchecked()
				},
			Err(TryExtendIter::FullCapacity { .. }) =>
				panic!("capacity overflow")
		}
	}
}

impl<T: Clone, const N: usize, A: Allocator, const ATOMIC: bool> IntoIterator for ArrayVec<T, N, ATOMIC, A> {
	type Item = T;
	type IntoIter = IntoIter<T, N, A, ATOMIC>;

	/// Consumes the vector into an iterator yielding elements by value. If the vector is shared,
	/// the elements are cloned out of the vector.
	fn into_iter(self) -> Self::IntoIter {
		if self.is_unique() {
			IntoIter::new_owned(self)
		} else {
			IntoIter::new_cloned(self)
		}
	}
}

impl<'a, T, const N: usize, A: Allocator, const ATOMIC: bool> IntoIterator for &'a ArrayVec<T, N, ATOMIC, A> {
	type Item = &'a T;
	type IntoIter = Iter<'a, T>;

	fn into_iter(self) -> Self::IntoIter {
		self.as_slice().iter()
	}
}

impl<'a, T: Clone, const N: usize, A: Allocator + Clone, const ATOMIC: bool> IntoIterator for &'a mut ArrayVec<T, N, ATOMIC, A> {
	type Item = &'a mut T;
	type IntoIter = IterMut<'a, T>;

	/// # Panics
	///
	/// Panics if allocation fails, for example in an out-of-memory condition.
	fn into_iter(self) -> Self::IntoIter {
		self.as_mut_slice().iter_mut()
	}
}

impl<T: Clone, const N: usize, A: Allocator + Clone, const ATOMIC: bool> Extend<T> for ArrayVec<T, N, ATOMIC, A> {
	#[allow(clippy::panic)]
	fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
		for elem in iter {
			if self.push(elem).is_err() {
				panic!("capacity overflowed");
			}
		}
	}
}

impl<'a, T: Copy + 'a, const N: usize, A: Allocator + Clone, const ATOMIC: bool> Extend<&'a T> for ArrayVec<T, N, ATOMIC, A> {
	#[allow(clippy::panic)]
	fn extend<I: IntoIterator<Item = &'a T>>(&mut self, iter: I) {
		for elem in iter {
			if self.push(*elem).is_err() {
				panic!("capacity overflowed");
			}
		}
	}
}

impl<T: Eq, const N: usize, A: Allocator, const ATOMIC: bool> Eq for ArrayVec<T, N, ATOMIC, A> { }

impl<T, const N1: usize, const N2: usize, A1, A2, const ATOMIC1: bool, const ATOMIC2: bool> PartialOrd<ArrayVec<T, N2, ATOMIC2, A2>> for ArrayVec<T, N1, ATOMIC1, A1>
where
	T: PartialOrd,
	A1: Allocator,
	A2: Allocator
{
	fn partial_cmp(&self, other: &ArrayVec<T, N2, ATOMIC2, A2>) -> Option<Ordering> {
		PartialOrd::partial_cmp(&**self, &**other)
	}
}

impl<T: Ord, const N: usize, A: Allocator, const ATOMIC: bool> Ord for ArrayVec<T, N, ATOMIC, A> {
	fn cmp(&self, other: &Self) -> Ordering {
		Ord::cmp(&**self, &**other)
	}
}

impl<T, const N: usize, A: Allocator, const ATOMIC: bool> Drop for ArrayVec<T, N, ATOMIC, A> {
	fn drop(&mut self) {
		self.inner.drop_ref::<ATOMIC>(&mut self.len);
	}
}

impl<T, const N: usize, const ATOMIC: bool> Default for ArrayVec<T, N, ATOMIC> {
	fn default() -> Self {
		Self::new()
	}
}

impl<T: fmt::Debug, const N: usize, A: Allocator, const ATOMIC: bool> fmt::Debug for ArrayVec<T, N, ATOMIC, A> {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		fmt::Debug::fmt(&**self, f)
	}
}

impl<T, const N: usize, A: Allocator, const ATOMIC: bool> AsRef<Self> for ArrayVec<T, N, ATOMIC, A> {
	fn as_ref(&self) -> &Self {
		self
	}
}

impl<T, const N: usize, A: Allocator, const ATOMIC: bool> AsMut<Self> for ArrayVec<T, N, ATOMIC, A> {
	fn as_mut(&mut self) -> &mut Self {
		self
	}
}

impl<T, const N: usize, A: Allocator, const ATOMIC: bool> AsRef<[T]> for ArrayVec<T, N, ATOMIC, A> {
	fn as_ref(&self) -> &[T] {
		self
	}
}

// Array and slice conversions

impl<T: Clone, const N: usize, const ATOMIC: bool> From<&[T; N]> for ArrayVec<T, N, ATOMIC> {
	fn from(value: &[T; N]) -> Self {
		// Safety: the array contains exactly `N` elements, so cannot overflow the
		//  vector.
		unsafe {
			Self::from_iter_trusted(value.iter().cloned())
		}
	}
}

impl<T: Clone, const N: usize, const ATOMIC: bool> From<&mut [T; N]> for ArrayVec<T, N, ATOMIC> {
	fn from(value: &mut [T; N]) -> Self {
		// Safety: the array contains exactly `N` elements, so cannot overflow the
		//  vector.
		unsafe {
			Self::from_iter_trusted(value.iter().cloned())
		}
	}
}

impl<T, const N: usize, const ATOMIC: bool> From<[T; N]> for ArrayVec<T, N, ATOMIC> {
	fn from(value: [T; N]) -> Self {
		// Safety: the array contains exactly `N` elements, so cannot overflow the
		//  vector.
		unsafe {
			Self::from_iter_trusted(value)
		}
	}
}

impl<T: Clone, const N1: usize, const N2: usize, A: Allocator, const ATOMIC: bool> TryFrom<ArrayVec<T, N1, ATOMIC, A>> for [T; N2] {
	type Error = ArrayVec<T, N1, ATOMIC, A>;

	/// Converts an [`ArrayVec`] into an array, cloning out of a shared allocation.
	/// 
	/// # Errors
	/// 
	/// Returns the vector back if its length is too large or small to fit in the array size.
	#[allow(clippy::multiple_unsafe_ops_per_block)]
	fn try_from(value: ArrayVec<T, N1, ATOMIC, A>) -> Result<Self, Self::Error> {
		if value.len() != N2 {
			return Err(value)
		}

		struct DropGuard<T> {
			ptr: *mut T,
			len: usize
		}

		impl<T> Drop for DropGuard<T> {
			fn drop(&mut self) {
				// Safety: `len` elements have been initialized.
				unsafe {
					let slice = ptr::slice_from_raw_parts_mut(self.ptr, self.len);
					self.len = 0;
					ptr::drop_in_place(slice);
				}
			}
		}

		// Can't use an array of `MaybeUninit`s because there's no stable way to `assume_init`
		// without copying.
		let mut array = MaybeUninit::<[T; N2]>::uninit();
		let ptr = array.as_mut_ptr().cast::<T>();

		match value.try_into_iter() {
			Ok(iter) => {
				for (i, elem) in iter.enumerate() {
					// Safety: initializing a `MaybeUninit`.
					unsafe {
						ptr.add(i).write(elem);
					}
				}
			}
			Err(vec) => {
				// Drop already cloned elements if `T::clone` panics.
				let DropGuard { len, .. } = &mut DropGuard { ptr, len: 0 };

				for (i, elem) in vec.iter().enumerate() {
					// Safety: initializing a `MaybeUninit`.
					unsafe {
						ptr.add(i).write(elem.clone());
					}
					*len += 1;
				}
			}
		}

		// Safety: all elements have been initialized.
		Ok(unsafe { array.assume_init() })
	}
}

impl<T: Clone, const N: usize, const ATOMIC: bool> TryFrom<&[T]> for ArrayVec<T, N, ATOMIC> {
	type Error = TryFromSlice<N>;

	fn try_from(value: &[T]) -> Result<Self, TryFromSlice<N>> {
		if value.len() > N {
			Err(TryFromSlice(value.len()))
		} else {
			// Safety: the slice length has been checked to not overflow the capacity.
			Ok(unsafe {
				Self::from_iter_trusted(value.iter().cloned())
			})
		}
	}
}

impl<T: Clone, const N: usize, const ATOMIC: bool> TryFrom<&mut [T]> for ArrayVec<T, N, ATOMIC> {
	type Error = TryFromSlice<N>;

	fn try_from(value: &mut [T]) -> Result<Self, TryFromSlice<N>> {
		if value.len() > N {
			Err(TryFromSlice(value.len()))
		} else {
			// Safety: the slice length has been checked to not overflow the capacity.
			Ok(unsafe {
				Self::from_iter_trusted(value.iter().cloned())
			})
		}
	}
}

impl<const N: usize, const ATOMIC: bool> TryFrom<&str> for ArrayVec<u8, N, ATOMIC> {
	type Error = TryFromSlice<N>;

	fn try_from(value: &str) -> Result<Self, Self::Error> {
		value.as_bytes().try_into()
	}
}

// Fallible Box/Vec conversions

impl<T, const N: usize, A: Allocator, const ATOMIC: bool> TryFrom<StdVec<T, A>> for ArrayVec<T, N, ATOMIC, A> {
	type Error = StdVec<T, A>;

	/// Creates a new vector from a [`Vec`](vec::Vec).
	///
	/// # Errors
	///
	/// Returns the [`Vec`](vec::Vec) back as an error if:
	/// - the length is greater than the fixed capacity `N`
	/// - the capacity is not equal to the fixed capacity `N`, and it failed to shrink or grow to
	///   exactly this amount
	#[allow(clippy::multiple_unsafe_ops_per_block)]
	fn try_from(mut value: StdVec<T, A>) -> Result<Self, StdVec<T, A>> {
		use alloc::alloc::handle_alloc_error;
		use core::alloc::Layout;
		use crate::raw::{check_size, VecInner};

		let len = value.len();
		if len > N {
			return Err(value)
		}

		// Todo: shrink to N + 3 bytes to skip growing if the vector memory is larger
		//  than N.

		if let Some(additional) = N.checked_sub(value.capacity()) {
			value.reserve_exact(additional);
		} else {
			value.shrink_to(N);
		}

		if value.capacity() != N {
			return Err(value)
		}

		let new_layout = Layout::new::<VecInner<[T; N]>>();
		if let Err(err) = check_size(new_layout.size()) {
			err.handle();
		}
		// Todo: account for padding between the prefix and array?
		let prefix_size = size_of::<VecInner>();

		// Grow the allocation back by three `usize` words.
		let (ptr, len, cap, alloc) = value.into_raw_parts_with_alloc();
		// Safety: the pointer was returned by `Vec`, so must be non-null.
		let ptr = unsafe {
			NonNull::new_unchecked(ptr)
		};
		let old_layout = Layout::new::<[T; N]>();
		// Safety: the pointer was allocated by `Vec` in the allocator with `old_layout`.
		//  `new_layout` is larger than `old_layout`.
		let Ok(ptr) = (unsafe {
			alloc.grow(ptr.cast(), old_layout, new_layout)
		}) else {
			handle_alloc_error(new_layout);
		};

		// Safety: the allocation is large enough to shift the elements back by the prefix size. The
		//  counts and length are initialized properly.
		unsafe {
			let byte_ptr = ptr.cast::<u8>().as_ptr();
			let start_ptr = byte_ptr.add(prefix_size);
			ptr::copy(
				byte_ptr,
				start_ptr,
				size_of::<[T; N]>()
			);

			let inner_ptr = ptr.cast::<VecInner>();
			VecInner::init_counts(inner_ptr);
			VecInner::len(inner_ptr).as_ptr().write(N);

			Ok(Self {
				inner: RawVec::<[T; N], _>::from_raw_parts(start_ptr.cast(), alloc),
				len,
			})
		}
	}
}

impl<const N: usize, const ATOMIC: bool> TryFrom<String> for ArrayVec<u8, N, ATOMIC> {
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

impl<T, const N: usize, const ATOMIC: bool> TryFrom<Box<[T]>> for ArrayVec<T, N, ATOMIC> {
	type Error = Box<[T]>;

	fn try_from(value: Box<[T]>) -> Result<Self, Box<[T]>> {
		let array_box = Box::<[T; N]>::try_from(value)?;
		Ok(array_box.into())
	}
}

impl<T, const N: usize, const ATOMIC: bool> From<Box<[T; N]>> for ArrayVec<T, N, ATOMIC> {
	#[allow(clippy::panic)]
	#[allow(clippy::multiple_unsafe_ops_per_block)]
	fn from(value: Box<[T; N]>) -> Self {
		use alloc::alloc::handle_alloc_error;
		use core::alloc::Layout;
		use crate::raw::VecInner;

		let new_layout = Layout::new::<VecInner<[T; N]>>();
		if let Err(err) = check_size(new_layout.size()) {
			err.handle();
		}
		// Todo: account for padding between the prefix and array?
		let prefix_size = size_of::<VecInner>();

		// Grow the allocation back by three `usize` words.
		let (ptr, alloc) = Box::into_non_null_with_allocator(value);
		let old_layout = Layout::new::<[T; N]>();
		// Safety: the pointer was allocated by `Box` in the allocator with `old_layout`.
		//  `new_layout` is larger than `old_layout`.
		let Ok(ptr) = (unsafe {
			alloc.grow(ptr.cast(), old_layout, new_layout)
		}) else {
			handle_alloc_error(new_layout);
		};

		// Safety: the allocation is large enough to shift the elements back by the prefix size. The
		//  counts and length are initialized properly.
		unsafe {
			let byte_ptr = ptr.cast::<u8>().as_ptr();
			let start_ptr = byte_ptr.add(prefix_size);
			ptr::copy(
				byte_ptr,
				start_ptr,
				size_of::<[T; N]>()
			);

			let inner_ptr = ptr.cast::<VecInner>();
			VecInner::init_counts(inner_ptr);
			VecInner::len(inner_ptr).as_ptr().write(N);
			
			Self {
				inner: RawVec::<[T; N], _>::from_raw_parts(start_ptr.cast(), alloc),
				len: N,
			}
		}
	}
}

impl<const N: usize, const ATOMIC: bool> TryFrom<Box<str>> for ArrayVec<u8, N, ATOMIC> {
	type Error = Box<str>;

	fn try_from(value: Box<str>) -> Result<Self, Box<str>> {
		Box::<[u8]>::from(value)
			.try_into()
			.map_err(|v|
				// Safety: the string was just converted into bytes and returned
				// back as an error unmodified.
				unsafe {
					mem::transmute(v)
				}
			)
	}
}

#[test]
fn unique_weak_copy_out_regression() {
	let mut vec = rc::ArrayVec::from([1, 2, 3]);
	let weak = vec.demote();
	vec.unique();

	assert_eq!(vec.weak_count(), 0);
	assert_eq!(vec, [1, 2, 3]);
}
