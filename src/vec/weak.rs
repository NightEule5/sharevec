// Copyright 2025 - Strixpyrr
// SPDX-License-Identifier: Apache-2.0

use alloc::alloc::Global;
use alloc::{rc, sync};
use core::alloc::Allocator;
use core::marker::PhantomData;
use core::{fmt, ptr};
use core::mem::ManuallyDrop;
use core::num::NonZeroUsize;
use core::ptr::NonNull;
#[cfg(feature = "array-vec")]
use crate::array::vec::ArrayVec;
use crate::raw::{InnerBase, RawVec, VecInner};
use crate::raw::inner::RawInnerVec;
use super::Vec;

pub struct Weak<T, A: Allocator, const ATOMIC: bool> {
	pub(crate) ptr: NonNull<VecInner>,
	pub(crate) _t: PhantomData<T>,
	pub(crate) cap: usize,
	pub(crate) alloc: ManuallyDrop<A>,
}

impl<T, const ATOMIC: bool> Weak<T, Global, ATOMIC> {
	/// Creates a new weak pointer referencing nothing.
	/// 
	/// Calling [`promote`](Self::promote) on the returned value always gives an empty vector.
	/// 
	/// # Examples
	/// 
	/// ```
	/// use sharevec::vec::rc::Weak;
	/// 
	/// let empty = Weak::<u32>::new();
	/// assert_eq!(empty.promote(), None);
	/// ```
	#[must_use]
	pub const fn new() -> Self {
		Self::new_in(Global)
	}

	/// Converts a raw pointer previously returned by [`into_raw_parts`] back into [`Weak`].
	/// 
	/// This can be used to safely get a strong reference (by calling [`promote`]) or to decrement
	/// the weak count by dropping the returned pointer.
	/// 
	/// This takes ownership of one weak reference (unless the pointer was created by [`new`]).
	/// 
	/// # Safety
	/// 
	/// The pointer must have been returned by [`into_raw`] and must still own its weak reference.
	/// It also must have been allocated by the global allocator.
	/// 
	/// The strong count may be `0` at the time of this call. However, this takes ownership of the
	/// weak reference represented by the raw pointer, and therefore it must be paired with a
	/// previous call to [`into_raw`].
	/// 
	/// # Examples
	/// 
	/// ```
	/// use sharevec::vec::rc::{Vec, Weak};
	///
	/// let strong = Vec::from(b"Hello!");
	///
	/// let raw1 = strong.demote().into_raw();
	/// let raw2 = strong.demote().into_raw();
	///
	/// assert_eq!(strong.weak_count(), 2);
	/// assert_eq!(unsafe { Weak::from_raw(raw1) }.promote().unwrap(), b"Hello!");
	/// assert_eq!(strong.weak_count(), 1); // One weak reference has been dropped.
	///
	/// drop(strong);
	///
	/// // Drop the last weak reference.
	/// assert!(unsafe { Weak::from_raw(raw2) }.promote().is_none());
	/// ```
	///
	/// [`into_raw`]: Self::into_raw
	/// [`promote`]: Self::promote
	/// [`new`]: Self::new
	pub unsafe fn from_raw(ptr: *const [T]) -> Self {
		Self::from_raw_in(ptr, Global)
	}
}

impl<T, A: Allocator, const ATOMIC: bool> Weak<T, A, ATOMIC> {
	/// Creates a new weak pointer referencing nothing, associated with the specified allocator.
	///
	/// Calling [`promote`](Self::promote) on the returned value always gives an empty vector.
	///
	/// # Examples
	///
	/// ```
	/// #![feature(allocator_api)]
	///
	/// # #[cfg(feature = "std")]
	/// # {
	/// use sharevec::vec::rc::Weak;
	/// use std::alloc::System;
	///
	/// let empty = Weak::<u32, _>::new_in(System);
	/// assert_eq!(empty.promote(), None);
	/// # }
	/// ```
	#[must_use]
	pub const fn new_in(alloc: A) -> Self {
		// `NonNull::without_provenance` is unstable.
		// Safety: we know `usize::MAX` is non-zero.
		let ptr = unsafe {
			let raw_ptr: *mut VecInner =
				ptr::without_provenance_mut(usize::MAX);
			NonNull::new_unchecked(raw_ptr)
		};
		Self { ptr, _t: PhantomData, cap: 0, alloc: ManuallyDrop::new(alloc) }
	}
	
	/// Returns a reference to the underlying allocator.
	pub fn allocator(&self) -> &A {
		&self.alloc
	}

	/// Returns a raw pointer to the referenced slice.
	/// 
	/// The pointer is valid only if there are strong references. Otherwise, the pointer may be
	/// dangling, unaligned, or [`null`](core::ptr::null).
	/// 
	/// # Examples
	/// 
	/// ```
	/// # #[cfg(feature = "std")]
	/// # {
	/// use sharevec::vec::rc::Vec;
	/// use std::ptr;
	///
	/// let strong = Vec::from(b"Hello!");
	/// let weak = strong.demote();
	/// // Both point to the same data.
	/// assert!(ptr::eq(&*strong, weak.as_ptr()));
	/// // The strong reference keeps the contents live, allowing access.
	/// assert_eq!(unsafe { &*weak.as_ptr() }, b"Hello!");
	///
	/// drop(strong);
	/// // No strong reference exists. Reading from the pointer would cause undefined
	/// // behavior now.
	/// # }
	/// ```
	#[must_use]
	pub fn as_ptr(&self) -> *const [T] {
		let thin_ptr = VecInner::store(self.ptr.cast());
		ptr::slice_from_raw_parts(thin_ptr.cast().as_ptr(), self.capacity())
	}
	
	/// Consumes the [`Weak`], returning its raw pointer.
	/// 
	/// This preserves ownership of the weak reference; the weak count is not decremented. It can be
	/// converted back to a [`Weak`] with [`from_raw`].
	/// 
	/// The same restrictions of accessing the target of the pointer as with [`as_ptr`] apply.
	/// 
	/// [`from_raw`]: Self::from_raw
	/// [`as_ptr`]: Self::as_ptr
	/// 
	/// # Examples
	/// 
	/// ```
	/// use sharevec::vec::rc::{Vec, Weak};
	///
	/// let strong = Vec::from(b"Hello!");
	/// let raw = strong.demote().into_raw();
	///
	/// assert_eq!(strong.weak_count(), 1);
	/// assert_eq!(unsafe { &*raw }, b"Hello!");
	///
	/// drop(unsafe { Weak::from_raw(raw) });
	/// assert_eq!(strong.weak_count(), 0);
	/// ```
	#[must_use = "losing the pointer will leak memory"]
	pub fn into_raw(self) -> *const [T] {
		let (ptr, _) = self.into_raw_with_allocator();
		ptr
	}

	/// Consumes the [`Weak`], returning its raw pointer and allocator.
	/// 
	/// This preserves ownership of the weak reference; the weak count is not decremented. It can be
	/// converted back to a [`Weak`] with [`from_raw_in`].
	/// 
	/// The same restrictions of accessing the target of the pointer as with [`as_ptr`] apply.
	/// 
	/// [`from_raw_in`]: Self::from_raw_in
	/// [`as_ptr`]: Self::as_ptr
	///
	/// # Examples
	///
	/// ```
	/// #![feature(allocator_api)]
	///
	/// # #[cfg(feature = "std")]
	/// # {
	/// use sharevec::vec::rc::{Vec, Weak};
	/// use std::alloc::System;
	///
	/// let mut strong = Vec::<u8, _>::new_in(System);
	/// strong.extend_from_slice(b"Hello!");
	/// let (raw, alloc) = strong.demote().into_raw_with_allocator();
	///
	/// assert_eq!(strong.weak_count(), 1);
	/// assert_eq!(unsafe { &(*raw)[..6] }, b"Hello!");
	///
	/// drop(unsafe { Weak::from_raw_in(raw, alloc) });
	/// assert_eq!(strong.weak_count(), 0);
	/// # }
	/// ```
	#[must_use = "losing the pointer will leak memory"]
	pub fn into_raw_with_allocator(self) -> (*const [T], A) {
		let mut md = ManuallyDrop::new(self);
		let ptr = md.as_ptr();
		// Safety: we semantically move `alloc` out while bypassing its dropper.
		let alloc = unsafe { ManuallyDrop::take(&mut md.alloc) };
		(ptr, alloc)
	}

	/// Converts a raw pointer previously returned by [`into_raw`] back into [`Weak`].
	///
	/// This can be used to safely get a strong reference (by calling [`promote`]) or to decrement
	/// the weak count by dropping the returned pointer.
	///
	/// This takes ownership of one weak reference (unless the pointer was created by [`new`]).
	///
	/// # Safety
	///
	/// The pointer must have been returned by [`into_raw`] and must still own its weak reference.
	/// It also must have been allocated by `alloc`.
	///
	/// The strong count may be `0` at the time of this call. However, this takes ownership of the
	/// weak reference represented by the raw pointer, and therefore it must be paired with a
	/// previous call to [`into_raw`].
	///
	/// # Examples
	///
	/// ```
	/// #![feature(allocator_api)]
	///
	/// # #[cfg(feature = "std")]
	/// # {
	/// use sharevec::vec::rc::{Vec, Weak};
	/// use std::alloc::System;
	///
	/// let mut strong = Vec::<u8, _>::new_in(System);
	/// strong.extend_from_slice(b"Hello!");
	///
	/// let (raw1, alloc1) = strong.demote().into_raw_with_allocator();
	/// let (raw2, alloc2) = strong.demote().into_raw_with_allocator();
	///
	/// assert_eq!(strong.weak_count(), 2);
	/// assert_eq!(unsafe { Weak::from_raw_in(raw1, alloc1) }.promote().unwrap(), b"Hello!");
	/// assert_eq!(strong.weak_count(), 1); // One weak reference has been dropped.
	///
	/// drop(strong);
	///
	/// // Drop the last weak reference.
	/// assert!(unsafe { Weak::from_raw_in(raw2, alloc2) }.promote().is_none());
	/// # }
	/// ```
	///
	/// [`into_raw`]: Self::into_raw
	/// [`promote`]: Self::promote
	/// [`new`]: Self::new
	pub unsafe fn from_raw_in(ptr: *const [T], alloc: A) -> Self {
		let cap = ptr.len();
		let ptr = VecInner::from_store(
			NonNull::new_unchecked(
				ptr.cast_mut()
			).cast()
		);
		Self { ptr, _t: PhantomData, cap, alloc: ManuallyDrop::new(alloc) }
	}

	/// Promotes the weak reference to a vector holding a strong reference to its contents.
	///
	/// Returns [`None`] if the contents have been dropped.
	/// 
	/// # Examples
	/// 
	/// ```
	/// use sharevec::vec::rc::Vec;
	/// 
	/// let mut vec = Vec::from(b"Hello!");
	/// let weak_vec = vec.demote();
	/// 
	/// let vec2 = weak_vec.promote();
	/// assert!(vec2.is_some());
	/// 
	/// // Destroy all strong references.
	/// drop(vec);
	/// drop(vec2);
	/// 
	/// assert!(weak_vec.promote().is_none())
	/// ```
	pub fn promote(&self) -> Option<Vec<T, ATOMIC, A>>
	where
		A: Clone,
	{
		(self.strong_count() != 0).then(|| {
			// Safety: the reference pointer was obtained from `demote` if the strong count is
			//  non-zero, so this pointer is valid.
			let mut vec = unsafe {
				RawVec::<[T], _>::from_non_null(
					VecInner::store(self.ptr.cast()).cast(),
					self.capacity(),
					(*self.alloc).clone()
				)
			};

			// Increment the strong count to delay dropping.
			vec.strong_inc::<ATOMIC>();

			Vec { inner: vec, len: self.len() }
		})
	}

	/// Returns the allocated capacity of the vector. 
	pub const fn capacity(&self) -> usize {
		self.cap
	}

	/// Returns the maximum length of the vector. 
	pub fn len(&self) -> usize {
		if is_dangling(self.ptr) {
			return 0
		}

		// Safety: the memory is always valid, as existence of a weak reference prevents it from
		//  being deallocated.
		unsafe {
			VecInner::len(self.ptr.cast()).as_ptr().read()
		}
	}

	/// Returns the number of strong references to the allocation.
	#[must_use]
	pub fn strong_count(&self) -> usize {
		if is_dangling(self.ptr) {
			0
		} else {
			// Safety: the reference is not dangling.
			unsafe {
				VecInner::strong_count::<ATOMIC>(self.ptr.cast())
			}
		}
	}
	/// Returns the number of weak references to the allocation, or `0` if there are no remaining
	/// strong pointers.
	#[must_use]
	pub fn weak_count(&self) -> usize {
		if self.strong_count() == 0 {
			0
		} else {
			// Safety: the reference is not dangling.
			unsafe {
				VecInner::weak_count::<ATOMIC>(self.ptr.cast())
			}
		}
	}

	/// Returns `true` if this weak pointer points to the same allocation as `other`, or if both
	/// pointers dangle (because they were created with [`Weak::new`]).
	/// 
	/// # Examples
	/// 
	/// ```
	/// use sharevec::vec::rc::{Vec, Weak};
	/// 
	/// let first_vec = Vec::from(b"Hello!");
	/// let first = first_vec.demote();
	/// let second = first_vec.demote();
	/// assert!(first.ptr_eq(&second));
	/// 
	/// let third = Vec::from(b"Hello!").demote();
	/// assert!(!first.ptr_eq(&third));
	/// ```
	/// 
	/// [`Weak::new`]:
	/// 
	/// ```
	/// use sharevec::vec::rc::{Vec, Weak};
	/// 
	/// let first = Weak::new();
	/// let second = Weak::new();
	/// assert!(first.ptr_eq(&second));
	/// 
	/// // Vec::new creates a dangling pointer too
	/// let third = Vec::<u32>::new().demote();
	/// assert!(first.ptr_eq(&third));
	/// ```
	#[must_use]
	pub fn ptr_eq(&self, other: &Self) -> bool {
		self.ptr == other.ptr
	}
	
	// Todo: add into_weak_array_vec?
}

fn is_dangling<T>(ptr: NonNull<T>) -> bool {
	ptr.cast::<()>().addr() == NonZeroUsize::MAX
}

impl<T, A: Allocator, const ATOMIC: bool> Drop for Weak<T, A, ATOMIC> {
	fn drop(&mut self) {
		if is_dangling(self.ptr) {
			// Safety: we are manually dropping the allocator, and never touch it again.
			unsafe {
				ManuallyDrop::drop(&mut self.alloc);
			}
			return
		}

		if unsafe { VecInner::weak_dec::<ATOMIC>(self.ptr) } != 0 {
			return
		}
		
		let cap = self.capacity();

		// If there are no strong references, deallocate the memory.
		if self.strong_count() == 0 {
			// Safety: we semantically move the allocator and never touch it from this field.
			let alloc = unsafe {
				ManuallyDrop::take(&mut self.alloc)
			};
			// Safety: there are no strong references to this memory. The memory is currently
			//  allocated.
			unsafe {
				let mut vec = RawInnerVec::from_non_null(self.ptr.cast(), alloc);
				RawVec::<[T], A>::deallocate(false, &mut vec, cap);
			}
		}
	}
}

impl<T, A: Allocator + Clone, const ATOMIC: bool> Clone for Weak<T, A, ATOMIC> {
	fn clone(&self) -> Self {
		// Clone the allocator first, in case it panics. In this case, the weak
		// count is not incremented.
		let alloc = self.alloc.clone();

		if !is_dangling(self.ptr) {
			// Safety: `ptr` is checked as non-dangling.
			unsafe {
				VecInner::weak_inc::<ATOMIC>(self.ptr);
			}
		}

		Self { alloc, ..*self }
	}
}

impl<T, A: Allocator, const ATOMIC: bool> fmt::Debug for Weak<T, A, ATOMIC> {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		write!(f, "(Weak)")
	}
}

impl<T, const ATOMIC: bool> Default for Weak<T, Global, ATOMIC> {
	fn default() -> Self {
		Self::new()
	}
}

impl<T, A: Allocator> From<Weak<T, A, false>> for rc::Weak<[T], A> {
	fn from(value: Weak<T, A, false>) -> Self {
		todo!()
	}
}

impl<T, A: Allocator> From<rc::Weak<[T], A>> for Weak<T, A, false>  {
	fn from(value: rc::Weak<[T], A>) -> Self {
		todo!()
	}
}

impl<T, A: Allocator> From<Weak<T, A, true>> for sync::Weak<[T], A> {
	fn from(value: Weak<T, A, true>) -> Self {
		todo!()
	}
}

impl<T, A: Allocator> From<sync::Weak<[T], A>> for Weak<T, A, true>  {
	fn from(value: sync::Weak<[T], A>) -> Self {
		todo!()
	}
}
