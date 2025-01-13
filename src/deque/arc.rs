// Copyright 2024 - Strixpyrr
// SPDX-License-Identifier: Apache-2.0

use alloc::alloc::Global;
use alloc::sync::Arc;
use core::alloc::Allocator;

/// A double-ended queue, implemented with a growable, reference-counted ring buffer. Can be cheaply
/// cloned in *O*(1) time, sharing its contents between clones. As a consequence, cloning is allowed
/// even when the element type lacks [`Clone`].
///
/// Queue containing a *unique* reference can be used as a [`VecDeque`] would be, with *O*(1) index,
/// push to either end, and pop operations. In addition, unlike [`VecDeque`], it can be cheaply
/// cloned in *O*(1) time, sharing its memory with its clones.
///
/// Queues containing a *shared* reference become clone-on-write. Pop operations from both ends
/// are still *O*(1), cloning the removed element, but any other modifying operation requires an
/// *O*(*n*) clone of the deque contents. Thus, when shared, the element type must implement
/// [`Clone`] for modification. As with [`Arc`], the vector may also be downgraded to a *weak*
/// reference, preventing another referring deque from deallocating its capacity but otherwise
/// allowing it to act as unique.
///
/// This type is thread-safe, and can safely share memory across threads; it implements [`Send`] and
/// [`Sync`] if [`T`] also implements these. Unless this is an explicit requirement, it is usually
/// preferable to use [`RcDeque`] instead, as atomic operations are more expensive than simple
/// memory accesses.
///
/// [`RcDeque`]: crate::deque::rc::ArrayDeque
///
/// # Uniqueness
///
/// See the module-level [uniqueness](crate::deque#uniqueness) section.
pub type Deque<T, A = Global> = super::Deque<T, true, A>;

// These should be implemented automatically, but constant generics might obscure the underlying Arc
// from the compiler.
unsafe impl<T: Send + Sync, A: Allocator + Send> Send for Deque<T, A> { }
unsafe impl<T: Send + Sync, A: Allocator + Sync> Sync for Deque<T, A> { }

/// An iterator over a drained range in [`Deque`], obtained by [`Deque::drain`]/[`try_drain`] or
/// [`Unique::drain`].
///
/// [`try_drain`]: Deque::try_drain
pub type Drain<'a, T, A = Global> = super::Drain<'a, T, A, true>;

/// An iterator which moves or clones the contents out of a [`Deque`], obtained by
/// [`Deque::into_iter`]/[`try_into_iter`] or [`Unique::into_iter`].
///
/// [`try_into_iter`]: Deque::try_into_iter
pub type IntoIter<T, A = Global> = super::IntoIter<T, A, true>;

/// A mutable view over a [`Deque`] with a unique reference, obtained by [`Deque::unique`] or
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
pub type Unique<'a, T, A = Global> = super::Unique<'a, T, A, true>;

/// A non-owning reference to the contents of an [`Deque`], obtained by [`Deque::demote`] or
/// [`Unique::demote`].
pub type Weak<T, A = Global> = super::Weak<T, A, true>;

impl<T, A: Allocator> Deque<T, A> {
	/// Returns a weak reference to the allocation. This does not count toward strong sharing, but
	/// guarantees that the underlying memory will not be deallocated.
	///
	/// Equivalent to [`Arc::downgrade`].
	///
	/// # Examples
	///
	/// ```
	/// use sharevec::deque::rc::Deque;
	///
	/// let mut vec = Deque::new();
	/// let weak_vec = vec.demote();
	///
	/// assert_eq!(vec.try_push_back(1), Ok(()));
	/// ```
	pub fn demote(&self) -> Weak<T, A> {
		todo!()
	}
}

impl<T, A: Allocator> Unique<'_, T, A> {
	/// Consumes the reference, returning a weak reference to the allocation.
	///
	/// Equivalent to [`Arc::downgrade`].
	pub fn demote(self) -> Weak<T, A> {
		todo!()
	}
}

impl<T, const N: usize, A: Allocator> From<Arc<[T; N], A>> for Deque<T, A> {
	fn from(value: Arc<[T; N], A>) -> Self {
		todo!()
	}
}

impl<T, const N: usize, A: Allocator> TryFrom<Deque<T, A>> for Arc<[T; N], A> {
	type Error = Deque<T, A>;

	/// Converts a [`Deque`] into an [`Arc<[T; N>`](Arc).
	///
	/// # Errors
	///
	/// Returns the deque back as an error if it holds a shared reference to its buffer, of it is
	/// too large to fit into the array.
	fn try_from(value: Deque<T, A>) -> Result<Self, Self::Error> {
		todo!()
	}
}

impl<T, A: Allocator> From<Arc<[T], A>> for Deque<T, A> {
	fn from(value: Arc<[T], A>) -> Self {
		todo!()
	}
}

impl<A: Allocator> From<Arc<str, A>> for Deque<u8, A> {
	fn from(value: Arc<str, A>) -> Self {
		todo!()
	}
}

impl<T, A: Allocator> TryFrom<Deque<T, A>> for Arc<[T], A> {
	type Error = Deque<T, A>;

	/// Converts a [`Deque`] into an [`Arc<[T]>`](Arc).
	///
	/// # Errors
	///
	/// Returns the deque back as an error if it holds a shared reference to its buffer.
	fn try_from(value: Deque<T, A>) -> Result<Self, Self::Error> {
		todo!()
	}
}
