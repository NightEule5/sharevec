// Copyright 2024 - Strixpyrr
// SPDX-License-Identifier: Apache-2.0

use alloc::alloc::Global;
use alloc::sync::Arc;
use core::alloc::Allocator;
use crate::error::Result;

/// A double-ended queue, implemented with a fixed-capacity, atomic reference-counted ring buffer.
/// Can be cheaply cloned in *O*(1) time, sharing its contents between clones. As a consequence,
/// cloning is allowed even when the element type lacks [`Clone`].
///
/// Queue containing a *unique* reference can be used as a [`VecDeque`] would be, with *O*(1) index,
/// push to either end, and pop operations. In addition, unlike [`VecDeque`], it can be cheaply
/// cloned in *O*(1) time, sharing its memory with its clones.
///
/// Queues containing a *shared* reference become clone-on-write. Pop operations from both ends
/// are still *O*(1), cloning the removed element, but any other modifying operation requires an
/// *O*(*n*) clone of the vector contents. Thus, when shared, the element type must implement
/// [`Clone`] for modification.
///
/// This type is thread-safe, and can safely share memory across threads; it implements [`Send`] and
/// [`Sync`] if [`T`] also implements these. Unless this is an explicit requirement, it is usually
/// preferable to use [`RcArrayDeque`] instead, as atomic operations are more expensive than simple
/// memory accesses.
///
/// [`RcArrayDeque`]: crate::array::vec::rc::ArrayDeque
pub type ArrayDeque<T, const N: usize, A = Global> = super::ArrayDeque<T, N, true, A>;

// These should be implemented automatically, but constant generics might obscure the underlying Arc
// from the compiler.
unsafe impl<T: Send + Sync, const N: usize, A: Allocator + Send> Send for ArrayDeque<T, N, A> { }
unsafe impl<T: Send + Sync, const N: usize, A: Allocator + Sync> Sync for ArrayDeque<T, N, A> { }

/// An iterator over a drained range in [`ArrayDeque`], obtained by [`ArrayDeque::drain`]/[`try_drain`]
/// or [`Unique::drain`].
///
/// [`try_drain`]: ArrayDeque::try_drain
pub type Drain<'a, T, const N: usize, A = Global> = super::Drain<'a, T, N, A, true>;

/// An iterator which moves or clones the contents out of an [`ArrayDeque`], obtained by
/// [`ArrayDeque::into_iter`]/[`try_into_iter`] or [`Unique::into_iter`].
///
/// [`try_into_iter`]: ArrayDeque::try_into_iter
pub type IntoIter<T, const N: usize, A = Global> = super::IntoIter<T, N, A, true>;

/// A mutable view over an [`ArrayDeque`] with a unique reference, obtained by [`ArrayDeque::unique`] or
/// [`ArrayDeque::as_unique`].
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
pub type Unique<'a, T, const N: usize, A = Global> = super::Unique<'a, T, N, A, true>;

// Same rules as `&mut ArrayDeque`
// Todo: check if these explicit impls are automatically implemented.
unsafe impl<T, const N: usize, A: Allocator> Send for Unique<'_, T, N, A>
where ArrayDeque<T, N, A>: Send { }
unsafe impl<T, const N: usize, A: Allocator> Sync for Unique<'_, T, N, A>
where ArrayDeque<T, N, A>: Sync { }

/// A non-owning reference to the contents of an [`ArrayDeque`], obtained by [`ArrayDeque::demote`]
/// or [`Unique::demote`].
pub type Weak<T, const N: usize, A = Global> = super::Weak<T, N, A, true>;

impl<T, const N: usize, A: Allocator> ArrayDeque<T, N, A> {
	/// Returns a weak reference to the allocation. This does not count toward strong sharing, but
	/// guarantees that the underlying memory will not be deallocated.
	///
	/// Equivalent to [`Arc::downgrade`].
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::array::deque::arc::ArrayDeque;
	///
	/// let mut deque = ArrayDeque::<_, 1>::new();
	/// let weak_deque = deque.demote();
	///
	/// assert_eq!(deque.try_push_back(1), Ok(()));
	/// ```
	pub fn demote(&self) -> Weak<T, N, A> {
		todo!()
	}
}

impl<T, const N: usize, A: Allocator> Unique<'_, T, N, A> {
	/// Consumes the reference, returning a weak reference to the allocation.
	///
	/// Equivalent to [`Arc::downgrade`].
	pub fn demote(self) -> Weak<T, N, A> {
		todo!()
	}
}

impl<T, const N: usize, A: Allocator> From<Arc<[T; N], A>> for ArrayDeque<T, N, A> {
	fn from(value: Arc<[T; N], A>) -> Self {
		todo!()
	}
}

impl<T, const N: usize, A: Allocator> TryFrom<ArrayDeque<T, N, A>> for Arc<[T; N], A> {
	type Error = ArrayDeque<T, N, A>;

	fn try_from(value: ArrayDeque<T, N, A>) -> Result<Self, Self::Error> {
		todo!()
	}
}

impl<T, const N: usize, A: Allocator> TryFrom<Arc<[T], A>> for ArrayDeque<T, N, A> {
	type Error = Arc<[T], A>;

	fn try_from(value: Arc<[T], A>) -> Result<Self, Arc<[T], A>> {
		todo!()
	}
}

impl<const N: usize, A: Allocator> TryFrom<Arc<str, A>> for ArrayDeque<u8, N, A> {
	type Error = Arc<str, A>;

	fn try_from(value: Arc<str, A>) -> Result<Self, Arc<str, A>> {
		todo!()
	}
}

impl<T, const N: usize, A: Allocator> From<ArrayDeque<T, N, A>> for Arc<[T], A> {
	/// Note: the vector array is coerced into a slice, as it may not be full. If the full array is
	/// desired, a [`TryFrom`] implementation exists for this conversion.
	fn from(value: ArrayDeque<T, N, A>) -> Self {
		todo!()
	}
}
