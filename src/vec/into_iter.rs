// Copyright 2025 - Strixpyrr
// SPDX-License-Identifier: Apache-2.0

use core::alloc::Allocator;
use core::{fmt, ptr, slice};
use core::fmt::Debug;
use core::iter::FusedIterator;
#[cfg(feature = "unstable-traits")]
use core::iter::TrustedLen;
use core::marker::PhantomData;
use core::mem::{ManuallyDrop, MaybeUninit};
#[cfg(feature = "unstable-traits")]
use core::num::NonZero;
#[cfg(feature = "unstable-traits")]
use core::ops::Try;
use core::ptr::NonNull;
use crate::error::{Result, Shared};
use crate::internal::{TypeSize, UnsafeClone};
use crate::raw::RawVec;
use super::Vec;

pub struct IntoIter<T, A: Allocator, const ATOMIC: bool> {
	mode: Mode,
	buf: NonNull<T>,
	_t: PhantomData<T>,
	cap: usize,
	alloc: ManuallyDrop<A>,
	ptr: NonNull<T>,
	end: *const T,
}

#[derive(Copy, Clone)]
enum Mode {
	Owned,
	Cloned
}

impl<T: fmt::Debug, A: Allocator, const ATOMIC: bool> fmt::Debug for IntoIter<T, A, ATOMIC> {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		f.debug_tuple("IntoIter").field(&self.as_slice()).finish()
	}
}

impl<T, A: Allocator, const ATOMIC: bool> IntoIter<T, A, ATOMIC> {
	pub(super) fn new_owned(vec: Vec<T, ATOMIC, A>) -> Self {
		Self::new(Mode::Owned, vec)
	}

	pub(super) fn new_cloned(vec: Vec<T, ATOMIC, A>) -> Self where T: Clone {
		Self::new(Mode::Cloned, vec)
	}

	#[allow(clippy::multiple_unsafe_ops_per_block)]
	fn new(mode: Mode, vec: Vec<T, ATOMIC, A>) -> Self {
		unsafe {
			let md = ManuallyDrop::new(vec);
			let alloc = ManuallyDrop::new(ptr::read(md.allocator()));
			let buf = md.inner.ptr();
			let cap = md.capacity();
			let start = buf.as_ptr();
			let end = if T::IS_ZST {
				start.wrapping_byte_add(md.len())
			} else {
				start.add(md.len()) as *const T
			};
			Self { mode, buf, _t: PhantomData, cap, alloc, ptr: buf, end }
		}
	}
	
	/// Returns the remaining elements as a slice.
	pub fn as_slice(&self) -> &[T] {
		// Safety: elements within `len` are initialized.
		unsafe { slice::from_raw_parts(self.ptr.as_ptr(), self.len()) }
	}

	/// Returns the remaining elements as a mutable slice, if the source vector is not shared.
	///
	/// # Errors
	///
	/// Returns an error if the vector holds a shared reference to its buffer.
	pub fn try_as_mut_slice(&mut self) -> Result<&mut [T]> {
		match self.mode {
			Mode::Owned => {
				debug_assert!(self.is_unique(), "vector must be unique");
				// Safety: elements within `len` are initialized.
				Ok(unsafe {
					slice::from_raw_parts_mut(self.ptr.as_ptr(), self.len())
				})
			}
			Mode::Cloned => Err(Shared(()))
		}
	}

	/// Returns a reference to the underlying allocator.
	pub fn allocator(&self) -> &A {
		&self.alloc
	}

	#[allow(clippy::multiple_unsafe_ops_per_block)]
	fn is_unique(&self) -> bool {
		matches!(&self.mode, Mode::Owned)
	}

	unsafe fn end_ptr(&self) -> NonNull<T> {
		NonNull::new_unchecked(self.end.cast_mut())
	}

	fn is_at_end(&self) -> bool {
		ptr::eq(self.ptr.as_ptr().cast_const(), self.end)
	}

	unsafe fn move_or_clone_slice(&self, ptr: NonNull<T>, target: &mut [MaybeUninit<T>]) {
		match self.mode {
			Mode::Owned =>
				ptr::copy_nonoverlapping(
					ptr.as_ptr(),
					target.as_mut_ptr().cast(),
					target.len()
				),
			Mode::Cloned =>
				for (i, elem) in target.iter_mut().enumerate() {
					elem.write((*ptr.as_ptr().add(i)).clone_unsafe());
				}
		}
	}
}

impl<T, A: Allocator, const ATOMIC: bool> AsRef<[T]> for IntoIter<T, A, ATOMIC> {
	fn as_ref(&self) -> &[T] {
		self.as_slice()
	}
}

impl<T, A: Allocator, const ATOMIC: bool> Iterator for IntoIter<T, A, ATOMIC> {
	type Item = T;

	#[allow(clippy::multiple_unsafe_ops_per_block)]
	fn next(&mut self) -> Option<T> {
		if self.is_at_end() {
			return None
		}
		let ptr = if T::IS_ZST {
			// `ptr` has to stay where it is to remain aligned, so we reduce the length by 1 by
			// reducing the `end`.
			self.end = self.end.cast::<u8>().wrapping_sub(1).cast();
			self.ptr
		} else {
			let old = self.ptr;
			// Safety: the pointer is not yet at the end of the vector, so this increment is valid.
			self.ptr = unsafe { old.add(1) };
			old
		};

		Some(match self.mode {
			Mode::Owned =>
				// Safety: the pointer is not at the end of the vector, so this element is valid.
				unsafe { ptr.as_ptr().read() },
			Mode::Cloned =>
				// Safety: the pointer is not at the end of the vector, so this element is valid.
				//  the mode can only be `Cloned` if `T` implements `Clone` at the time of creation
				//  of the iterator.
				unsafe {
					ptr.as_ref().clone_unsafe()
				}
		})
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let len = self.len();
		(len, Some(len))
	}

	fn count(self) -> usize {
		self.len()
	}

	#[allow(clippy::multiple_unsafe_ops_per_block)]
	#[cfg(feature = "unstable-traits")]
	fn advance_by(&mut self, n: usize) -> core::result::Result<(), NonZero<usize>> {
		let step_size = self.len().min(n);
		let to_drop = ptr::slice_from_raw_parts_mut(self.ptr.as_ptr(), step_size);
		if T::IS_ZST {
			// See `next` for why we sub `end` here.
			self.end = self.end.cast::<u8>().wrapping_sub(step_size).cast();
		} else {
			// Safety: the `min` above ensures that step_size is in bounds.
			self.ptr = unsafe { self.ptr.add(step_size) };
		}

		if matches!(self.mode, Mode::Owned) {
			// Safety: the `min` above ensures that step_size is in bounds.
			unsafe {
				ptr::drop_in_place(to_drop);
			}
		}

		NonZero::new(n - step_size).map_or(Ok(()), Err)
	}

	#[allow(clippy::multiple_unsafe_ops_per_block)]
	#[cfg(feature = "unstable-traits")]
	fn try_fold<B, F, R>(&mut self, mut init: B, mut f: F) -> R
	where
		Self: Sized,
		F: FnMut(B, Self::Item) -> R,
		R: Try<Output = B>,
	{
		if T::IS_ZST {
			while !self.is_at_end() {
				// Safety: we just checked that `self.ptr` is in bounds.
				let tmp = unsafe { self.ptr.read() };
				// See `next` for why we subtract from `end` here.
				self.end = self.end.cast::<u8>().wrapping_sub(1).cast();
				init = f(init, tmp)?;
			}
		} else {
			// Safety: `self.end` can only be null if `T` is a ZST.
			while !self.is_at_end() {
				// Safety: we just checked that `self.ptr` is in bounds.
				let tmp = unsafe { self.ptr.read() };
				// Increment `self.ptr` first to avoid double dropping in the event of a panic.
				// Safety: the maximum this can be is `self.end`.
				self.ptr = unsafe { self.ptr.add(1) };
				init = f(init, tmp)?;
			}
		}
		R::from_output(init)
	}

	#[allow(clippy::multiple_unsafe_ops_per_block)]
	fn fold<B, F>(mut self, mut init: B, mut f: F) -> B
	where
		F: FnMut(B, Self::Item) -> B,
	{
		if T::IS_ZST {
			while self.is_at_end() {
				// Safety: we just checked that `self.ptr` is in bounds.
				let tmp = unsafe { self.ptr.read() };
				// See `next` for why we subtract from `end` here.
				self.end = self.end.cast::<u8>().wrapping_sub(1).cast();
				init = f(init, tmp);
			}
		} else {
			// Safety: `self.end` can only be null if `T` is a ZST.
			while self.is_at_end() {
				// Safety: we just checked that `self.ptr` is in bounds.
				let tmp = unsafe { self.ptr.read() };
				// Increment `self.ptr` first to avoid double dropping in the event of a panic.
				// Safety: the maximum this can be is `self.end`.
				self.ptr = unsafe { self.ptr.add(1) };
				init = f(init, tmp);
			}
		}
		init
	}
}

impl<T, A: Allocator, const ATOMIC: bool> DoubleEndedIterator for IntoIter<T, A, ATOMIC> {
	#[allow(clippy::multiple_unsafe_ops_per_block)]
	fn next_back(&mut self) -> Option<Self::Item> {
		if self.is_at_end() {
			return None
		}
		if T::IS_ZST {
			// `ptr` has to stay where it is to remain aligned, so we reduce the length by 1 by
			// reducing the `end`.
			self.end = self.end.cast::<u8>().wrapping_sub(1).cast();
			// Note that even though this is next_back() we're reading from `self.ptr`, not
			// `self.end`. We track our length using the byte offset from `self.ptr` to `self.end`,
			// so the end pointer may not be suitably aligned for T.
			Some(match self.mode {
				Mode::Owned =>
					// Safety: the pointer is not at the start of the vector, so this element is
					//  valid.
					unsafe { self.ptr.read() },
				Mode::Cloned =>
					// Safety: the pointer is not at the start of the vector, so this element is
					//  valid. the mode can only be `Cloned` if `T` implements `Clone` at the time
					//  of creation of the iterator.
					unsafe {
						self.ptr.as_ref().clone_unsafe()
					}
			})
		} else {
			// Safety: the pointer is not at the start of the vector, so this element is
			//  valid. the mode can only be `Cloned` if `T` implements `Clone` at the time
			//  of creation of the iterator.
			unsafe {
				self.end = self.end.sub(1);
				Some(match self.mode {
					Mode::Owned  => self.end.read(),
					Mode::Cloned => (*self.end).clone_unsafe()
				})
			}
		}
	}

	#[cfg(feature = "unstable-traits")]
	fn advance_back_by(&mut self, n: usize) -> core::result::Result<(), NonZero<usize>> {
		let step_size = self.len().min(n);
		if T::IS_ZST {
			// SAFETY: same as for advance_by()
			self.end = self.end.cast::<u8>().wrapping_sub(step_size).cast();
		} else {
			// SAFETY: same as for advance_by()
			self.end = unsafe { self.end.sub(step_size) };
		}
		let to_drop = ptr::slice_from_raw_parts_mut(self.end as *mut T, step_size);

		if matches!(self.mode, Mode::Owned) {
			// SAFETY: same as for advance_by()
			unsafe {
				ptr::drop_in_place(to_drop);
			}
		}

		NonZero::new(n - step_size).map_or(Ok(()), Err)
	}
}

impl<T, A: Allocator, const ATOMIC: bool> ExactSizeIterator for IntoIter<T, A, ATOMIC> {
	fn len(&self) -> usize {
		// Can't use offset_from_unsigned for non-zst as it was stabilized too
		// recently.
		let byte_offset = (self.end as usize).wrapping_sub(self.ptr.as_ptr() as usize);
		if T::IS_ZST {
			byte_offset
		} else {
			// Can't use offset_from_unsigned as it was stabilized too recently.
			byte_offset / size_of::<T>()
		}
	}
}

#[cfg(feature = "unstable-traits")]
// Safety: this iterator always returns the number of elements given by size_hint.
unsafe impl<T, A: Allocator, const ATOMIC: bool> TrustedLen for IntoIter<T, A, ATOMIC> { }

impl<T, A: Allocator, const ATOMIC: bool> FusedIterator for IntoIter<T, A, ATOMIC> { }

// Todo: clone implementation?

impl<T, A: Allocator, const ATOMIC: bool> Drop for IntoIter<T, A, ATOMIC> {
	fn drop(&mut self) {
		use core::alloc::Layout;

		struct DropGuard<'a, T, A: Allocator, const ATOMIC: bool> {
			buf: NonNull<T>,
			cap: usize,
			alloc: &'a mut ManuallyDrop<A>,
		};

		impl<T, A: Allocator, const ATOMIC: bool> Drop for DropGuard<'_, T, A, ATOMIC> {
			fn drop(&mut self) {
				// Safety: `alloc` was taken from the iterator, and will not be touched again after
				//  moving.
				let alloc = unsafe {
					ManuallyDrop::take(self.alloc)
				};
				// Safety: the pointer references to valid, currently allocated memory returned from
				//  a vector.
				let mut vec = unsafe {
					RawVec::<[T], A>::from_non_null(self.buf, self.cap, alloc)
				};

				vec.drop_ref::<ATOMIC>(&mut 0);
			}
		}

		let len = self.len();
		let Self { mode, buf, cap, alloc, ptr, .. } = self;
		// Even if `drop_in_place` panics, the vector will be deallocated.
		let guard: DropGuard<T, A, ATOMIC> = DropGuard { buf: *buf, cap: *cap, alloc };

		if matches!(mode, Mode::Owned) {
			// Safety: elements within `len` are valid.
			unsafe {
				ptr::drop_in_place(ptr::slice_from_raw_parts_mut(ptr.as_ptr(), len));
			}
		}
	}
}
