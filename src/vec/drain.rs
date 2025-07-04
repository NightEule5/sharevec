// Copyright 2025 - Strixpyrr
// SPDX-License-Identifier: Apache-2.0

use alloc::vec;
use core::alloc::Allocator;
use core::{fmt, mem, ptr, slice};
use core::iter::FusedIterator;
#[cfg(feature = "unstable-traits")]
use core::iter::TrustedLen;
use core::marker::PhantomData;
use core::mem::ManuallyDrop;
#[cfg(feature = "unstable-traits")]
use core::num::NonZero;
use core::ops::Range;
use core::ptr::NonNull;
use core::slice::Iter;
use crate::internal::UnsafeClone;
use crate::raw::RawVec;
use super::Vec;

pub struct Drain<'a, T: 'a, A: Allocator + 'a, const ATOMIC: bool> {
	mode: Mode,
	tail: Range<usize>,
	iter: Iter<'a, T>,
	vec: NonNull<Vec<T, ATOMIC, A>>,
}

#[derive(Copy, Clone)]
enum Mode { Unique, Cloning }

impl<T: fmt::Debug, A: Allocator, const ATOMIC: bool> fmt::Debug for Drain<'_, T, A, ATOMIC> {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		f.debug_tuple("Drain").field(&self.iter.as_slice()).finish()
	}
}

impl<'a, T: 'a, A: Allocator + 'a, const ATOMIC: bool> Drain<'a, T, A, ATOMIC> {
	pub(super) fn unique(
		tail: Range<usize>,
		iter: Iter<'a, T>,
		vec: &'a mut Vec<T, ATOMIC, A>
	) -> Self {
		Self::new(Mode::Unique, tail, iter, vec)
	}

	pub(super) fn cloning(
		tail: Range<usize>,
		iter: Iter<'a, T>,
		vec: &'a mut Vec<T, ATOMIC, A>
	) -> Self {
		Self::new(Mode::Cloning, tail, iter, vec)
	}

	fn new(mode: Mode, tail: Range<usize>, iter: Iter<'a, T>, vec: &'a mut Vec<T, ATOMIC, A>) -> Self {
		Self {
			mode,
			tail,
			iter,
			vec: NonNull::from(vec),
		}
	}
}

impl<T, A: Allocator, const ATOMIC: bool> Drain<'_, T, A, ATOMIC> {
	/// Returns the remaining elements as a slice.
	#[must_use]
	pub fn as_slice(&self) -> &[T] {
		self.iter.as_slice()
	}

	/// Returns a reference to the underlying allocator.
	#[must_use]
	pub fn allocator(&self) -> &A {
		self.raw_vec().allocator()
	}

	// Todo: add keep_rest?
}

impl<T, A: Allocator, const ATOMIC: bool> AsRef<[T]> for Drain<'_, T, A, ATOMIC> {
	fn as_ref(&self) -> &[T] {
		self.as_slice()
	}
}

impl<T, A: Allocator, const ATOMIC: bool> Iterator for Drain<'_, T, A, ATOMIC> {
	type Item = T;

	fn next(&mut self) -> Option<Self::Item> {
		self.iter
			.next()
			.map(|v| move_or_clone(self.mode, v))
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let len = self.len();
		(len, Some(len))
	}
}

impl<T, A: Allocator, const ATOMIC: bool> DoubleEndedIterator for Drain<'_, T, A, ATOMIC> {
	fn next_back(&mut self) -> Option<Self::Item> {
		self.iter
			.next_back()
			.map(|v| move_or_clone(self.mode, v))
	}
}

impl<T, A: Allocator, const ATOMIC: bool> Drop for Drain<'_, T, A, ATOMIC> {
	fn drop(&mut self) {
		let tail = self.tail.clone();
		let iter = mem::take(&mut self.iter);
		// Safety: the pointer value is valid, and the reference is tied to a valid lifetime.
		let Vec { inner: vec, len: head_len } = unsafe {
			self.vec.as_mut()
		};

		match self.mode {
			Mode::Unique => drop_unique(tail, iter, vec, head_len),
			Mode::Cloning => drop_clone::<_, _, ATOMIC>(tail, vec, head_len)
		}
	}
}

impl<T, A: Allocator, const ATOMIC: bool> ExactSizeIterator for Drain<'_, T, A, ATOMIC> {
	fn len(&self) -> usize {
		self.iter.len()
	}

	#[cfg(feature = "unstable-traits")]
	fn is_empty(&self) -> bool {
		self.iter.is_empty()
	}
}

#[cfg(feature = "unstable-traits")]
// Safety: this iterator always returns the number of elements given by size_hint.
unsafe impl<T, A: Allocator, const ATOMIC: bool> TrustedLen for Drain<'_, T, A, ATOMIC> { }

impl<T, A: Allocator, const ATOMIC: bool> FusedIterator for Drain<'_, T, A, ATOMIC> { }

impl<T, A: Allocator, const ATOMIC: bool> Drain<'_, T, A, ATOMIC> {
	fn raw_vec(&self) -> &RawVec<[T], A> {
		// Safety: the pointer value is valid, and the reference is tied to a valid lifetime.
		unsafe {
			&self.vec.as_ref().inner
		}
	}
}

fn move_or_clone<T>(mode: Mode, v: &T) -> T {
	// If we have a unique reference, move with `ptr::read`. Otherwise, clone out of the
	// reference.
	match mode {
		Mode::Unique =>
			// Safety: the pointer comes from a reference, so it is valid for reads, properly
			// initialized and aligned.
			unsafe {
				ptr::read(v)
			},
		Mode::Cloning =>
			// Safety: in Clone mode, the type is checked to implement `Clone`.
			unsafe {
				v.clone_unsafe()
			}
	}
}

/// Drops a draining iterator through a unique reference, as [`vec::Drain`] does.
fn drop_unique<T, A: Allocator>(
	tail: Range<usize>,
	iter: Iter<T>,
	vec: &mut RawVec<[T], A>,
	len: &mut usize,
) {
	let old_len = *len;
	let drop_len = iter.len();

	if size_of::<T>() == 0 {
		// ZSTs are interchangeable; we only need to drop the correct amount. This can be done by
		// manipulating the vector's length instead of move them out of `iter`.
		unsafe {
			vec.set_len(len, old_len + drop_len + tail.len());
			vec.truncate(old_len + tail.len());
		}

		return
	}

	struct DropGuard<'a, T, A: Allocator> {
		tail: Range<usize>,
		vec: &'a mut RawVec<[T], A>,
		len: &'a mut usize,
	}

	impl<T, A: Allocator> Drop for DropGuard<'_, T, A> {
		fn drop(&mut self) {
			let Self { tail, vec, len } = self;
			if tail.len() > 0 {
				unsafe {
					let start = **len;
					let tail_start = tail.start;
					if tail_start != start {
						let src = vec.ptr().add(tail_start).as_ptr();
						let dst = vec.ptr().add(start).as_ptr();
						ptr::copy(src, dst, tail.len());
					}

					vec.set_len(len, start + tail.len());
				}
			}
		}
	}

	// Moves elements back to fill the dropped area, even if `ptr::drop_in_place` panics.
	let guard = DropGuard { tail, vec, len };

	let drop_ptr = iter.as_slice().as_ptr();

	unsafe {
		// `drop_ptr` comes from an immutable reference, but `ptr::drop_in_place` needs a pointer
		// valid for writes. We must reconstruct the pointer from the original vector, but avoid
		// creating a mutable reference to the front, as this would invalidate existing raw pointers.
		let vec_ptr = guard.vec.ptr().as_ptr();
		let drop_offset = drop_ptr.offset_from_unsigned(vec_ptr);
		let drop_slice = ptr::slice_from_raw_parts_mut(vec_ptr.add(drop_offset), drop_len);
		ptr::drop_in_place(drop_slice);
	}
}

/// Drops a draining iterator through a shared reference, by cloning the head and tail (if any) into
/// a new allocation, or setting the length if the tail is empty.
fn drop_clone<T, A: Allocator, const ATOMIC: bool>(
	tail: Range<usize>,
	vec: &mut RawVec<[T], A>,
	len: &mut usize,
) {
	struct AllocGuard<'alloc, T, A: Allocator> {
		vec: RawVec<[T], &'alloc A>
	}

	impl<T, A: Allocator> Drop for AllocGuard<'_, T, A> {
		fn drop(&mut self) {
			// No need for atomic operations, as we have a unique reference.
			self.vec.drop_ref::<false>(&mut 0);
		}
	}

	// If the tail is empty, there's nothing the move.
	if tail.is_empty() {
		return
	}

	let alloc = vec.allocator();
	// Todo: only allocate enough capacity for the head and tail?
	let dst = RawVec::<[T], &A>::with_capacity(vec.capacity(), alloc);
	// Deallocate the memory if `T::clone` panics.
	let mut dst = AllocGuard { vec: dst };
	let dst_ptr = dst.vec.ptr().as_ptr();

	// Clone the head to the target vector.
	//
	// source: [head] [yielded] [tail]
	// target: [head]
	let head_len = *len;
	unsafe {
		let head_src = slice::from_raw_parts(vec.ptr().as_ptr(), head_len);
		let head_dst = slice::from_raw_parts_mut(dst_ptr, head_len);
		UnsafeClone::clone_from_slice_unsafe(head_dst, head_src);
	}

	// Clone the tail to the end of the head in the target vector.
	//
	// source: [head] [yielded] [tail]
	// target: [head] [tail]
	let tail_len = tail.len();
	unsafe {
		let tail_src = slice::from_raw_parts(vec.ptr().add(tail.start).as_ptr(), tail_len);
		let tail_dst = slice::from_raw_parts_mut(dst_ptr.add(head_len), tail_len);
		UnsafeClone::clone_from_slice_unsafe(tail_dst, tail_src);
	}

	// No more risk of panicking, disarm the guard so we don't accidentally deallocate.
	let dst = ManuallyDrop::new(dst);
	let new_ptr = dst.vec.inner_ptr();

	unsafe {
		// Deallocate the source reference.
		vec.drop_ref::<ATOMIC>(len);
		// Replace the reference with the target allocation.
		vec.set_ptr(new_ptr.cast());
		vec.set_len(len, head_len + tail_len);
	}
}
