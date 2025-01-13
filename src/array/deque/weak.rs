// Copyright 2025 - Strixpyrr
// SPDX-License-Identifier: Apache-2.0

use alloc::alloc::Global;
use alloc::{rc, sync};
use core::alloc::Allocator;
use core::marker::PhantomData;
use core::fmt;
#[cfg(feature = "vec")]
use crate::deque::weak::Weak as DequeWeak;
use super::ArrayDeque;

pub struct Weak<T, const N: usize, A: Allocator, const ATOMIC: bool> {
	_t: PhantomData<T>,
	_a: PhantomData<A>
}

impl<T, const N: usize, const ATOMIC: bool> Weak<T, N, Global, ATOMIC> {
	/// Creates a new weak pointer referencing nothing.
	///
	/// Calling [`promote`](Self::promote) on the returned value always gives an empty deque.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::Weak;
	///
	/// let empty = Weak::<u32, 8>::new();
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
	/// use sharevec::array::deque::rc::{ArrayDeque, Weak};
	///
	/// let strong = ArrayDeque::from(b"Hello!");
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
	pub unsafe fn from_raw(ptr: *const [T; N]) -> Self {
		Self::from_raw_in(ptr, Global)
	}
}

impl<T, const N: usize, A: Allocator, const ATOMIC: bool> Weak<T, N, A, ATOMIC> {
	/// Creates a new weak pointer referencing nothing, associated with the specified allocator.
	///
	/// Calling [`promote`](Self::promote) on the returned value always gives an empty deque.
	///
	/// # Examples
	///
	/// ```
	/// #![feature(allocator_api)]
	///
	/// # #[cfg(feature = "std")]
	/// # {
	/// use sharevec::array::deque::rc::Weak;
	/// use std::alloc::System;
	///
	/// let empty = Weak::<u32, 8, _>::new_in(System);
	/// assert_eq!(empty.promote(), None);
	/// # }
	/// ```
	#[must_use]
	pub const fn new_in(alloc: A) -> Self {
		todo!()
	}

	/// Returns a reference to the underlying allocator.
	pub fn allocator(&self) -> &A {
		todo!()
	}

	/// Returns a raw pointer to the referenced array.
	///
	/// The pointer is valid only if there are strong references. Otherwise, the pointer may be
	/// dangling, unaligned, or [`null`](core::ptr::null).
	///
	/// # Examples
	///
	/// ```
	/// # #[cfg(feature = "std")]
	/// # {
	/// use sharevec::array::deque::rc::ArrayDeque;
	/// use std::ptr;
	///
	/// let strong = ArrayDeque::from(b"Hello!");
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
	pub fn as_ptr(&self) -> *const [T; N] {
		todo!()
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
	/// use sharevec::array::deque::rc::{ArrayDeque, Weak};
	///
	/// let strong = ArrayDeque::from(b"Hello!");
	/// let raw = strong.demote().into_raw();
	///
	/// assert_eq!(strong.weak_count(), 1);
	/// assert_eq!(unsafe { &*raw }, b"Hello!");
	///
	/// drop(unsafe { Weak::from_raw(raw) });
	/// assert_eq!(strong.weak_count(), 0);
	/// ```
	#[must_use = "losing the pointer will leak memory"]
	pub fn into_raw(self) -> *const [T; N] {
		todo!()
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
	/// # #![cfg(feature = "std")]
	/// # {
	/// use sharevec::array::deque::rc::{ArrayDeque, Weak};
	/// use std::alloc::System;
	///
	/// let mut strong = ArrayDeque::<u8, 6, _>::new_in(System);
	/// _ = strong.try_extend_from_slice(b"Hello!");
	/// let (raw, alloc) = strong.demote().into_raw_with_allocator();
	///
	/// assert_eq!(strong.weak_count(), 1);
	/// assert_eq!(unsafe { &*raw }, b"Hello!");
	///
	/// drop(unsafe { Weak::from_raw_in(raw, alloc) });
	/// assert_eq!(strong.weak_count(), 0);
	/// # }
	/// ```
	#[must_use = "losing the pointer will leak memory"]
	pub fn into_raw_with_allocator(self) -> (*const [T; N], A) {
		todo!()
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
	/// use sharevec::array::deque::rc::{ArrayDeque, Weak};
	/// use std::alloc::System;
	///
	/// let mut strong = ArrayDeque::<u8, 6, _>::new_in(System);
	/// _ = strong.try_extend_from_slice(b"Hello!");
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
	pub unsafe fn from_raw_in(ptr: *const [T; N], alloc: A) -> Self {
		todo!()
	}

	/// Promotes the weak reference to a deque holding a strong reference to its contents.
	///
	/// Returns [`None`] if the contents have been dropped.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let mut vec = ArrayDeque::from(b"Hello!");
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
	pub fn promote(&self) -> Option<ArrayDeque<T, N, ATOMIC, A>> {
		todo!()
	}

	/// Returns the maximum length of the deque. 
	pub fn len(&self) -> usize {
		todo!()
	}

	/// Returns the number of strong references to the allocation.
	#[must_use]
	pub fn strong_count(&self) -> usize {
		todo!()
	}
	/// Returns the number of weak references to the allocation, or `0` if there are no remaining
	/// strong pointers.
	#[must_use]
	pub fn weak_count(&self) -> usize {
		todo!()
	}

	/// Returns `true` if this weak pointer points to the same allocation as `other`, or if both
	/// pointers dangle (because they were created with [`Weak::new`]).
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::{ArrayDeque, Weak};
	///
	/// let first_vec = ArrayDeque::from(b"Hello!");
	/// let first = first_vec.demote();
	/// let second = first_vec.demote();
	/// assert!(first.ptr_eq(&second));
	///
	/// let third = ArrayDeque::from(b"Hello!").demote();
	/// assert!(!first.ptr_eq(&third));
	/// ```
	///
	/// [`Weak::new`]:
	///
	/// ```
	/// use sharevec::array::deque::rc::{ArrayDeque, Weak};
	///
	/// let first = Weak::new();
	/// let second = Weak::new();
	/// assert!(first.ptr_eq(&second));
	///
	/// let third = ArrayDeque::<u32, 5>::new().demote();
	/// assert!(!first.ptr_eq(&third));
	/// ```
	#[must_use]
	pub fn ptr_eq(&self, other: &Self) -> bool {
		todo!()
	}

	/// Converts the weak pointer into one for a resizable deque of capacity `N`.
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::rc::ArrayDeque;
	///
	/// let array_deque = ArrayDeque::<u32, 8>::new();
	/// let weak_deque = array_deque.demote().into_weak_deque();
	/// let vec = weak_deque.promote().unwrap();
	///
	/// assert_eq!(vec.capacity(), 8);
	/// ```
	#[cfg(feature = "vec")]
	pub fn into_weak_deque(self) -> DequeWeak<T, A, ATOMIC> {
		todo!()
	}
}

impl<T, const N: usize, A: Allocator, const ATOMIC: bool> Drop for Weak<T, N, A, ATOMIC> {
	fn drop(&mut self) {
		todo!()
	}
}

impl<T, const N: usize, A: Allocator + Clone, const ATOMIC: bool> Clone for Weak<T, N, A, ATOMIC> {
	fn clone(&self) -> Self {
		todo!()
	}
}

impl<T, const N: usize, A: Allocator, const ATOMIC: bool> fmt::Debug for Weak<T, N, A, ATOMIC> {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		write!(f, "(Weak)")
	}
}

impl<T, const N: usize, const ATOMIC: bool> Default for Weak<T, N, Global, ATOMIC> {
	fn default() -> Self {
		Self::new()
	}
}

impl<T, const N: usize, A: Allocator> From<Weak<T, N, A, false>> for rc::Weak<[T; N], A> {
	fn from(value: Weak<T, N, A, false>) -> Self {
		todo!()
	}
}

impl<T, const N: usize, A: Allocator> From<rc::Weak<[T; N], A>> for Weak<T, N, A, false> {
	fn from(value: rc::Weak<[T; N], A>) -> Self {
		// Todo: set length to N
		todo!()
	}
}

impl<T, const N: usize, A: Allocator> From<Weak<T, N, A, true>> for sync::Weak<[T; N], A> {
	fn from(value: Weak<T, N, A, true>) -> Self {
		todo!()
	}
}

impl<T, const N: usize, A: Allocator> From<sync::Weak<[T; N], A>> for Weak<T, N, A, true> {
	fn from(value: sync::Weak<[T; N], A>) -> Self {
		// Todo: set length to N
		todo!()
	}
}
