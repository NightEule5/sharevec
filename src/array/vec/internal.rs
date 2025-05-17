// Copyright 2025 - Strixpyrr
// SPDX-License-Identifier: Apache-2.0

use core::alloc::{AllocError, Allocator};
use core::mem::ManuallyDrop;
use core::ptr;
use crate::array::vec::ArrayVec;
use crate::error;
use crate::error::Shared;
use crate::raw::RawVec;

impl<T, const N: usize, const ATOMIC: bool> ArrayVec<T, N, ATOMIC> {
	#[track_caller]
	pub(super) unsafe fn from_iter_trusted(iter: impl IntoIterator<Item = T>) -> Self {
		let mut vec = Self::new();
		vec.inner.extend_trusted(&mut vec.len, iter);
		vec
	}
}

impl<T, const N: usize, A: Allocator, const ATOMIC: bool> ArrayVec<T, N, ATOMIC, A> {
	fn is_mutable(&self) -> bool {
		self.is_empty() || self.is_unique()
	}
	
	/// Checks whether the vector contents are mutable, either empty or unique. The vector length
	/// may not be allowed to grow in this case.
	pub(super) fn check_mutable(&self) -> error::Result {
		if self.is_mutable() {
			Ok(())
		} else {
			Err(Shared(()))
		}
	}
	
	/// Makes the current vector contents mutable, without necessarily allowing it to grow.
	/// 
	/// This avoids cloning where a shared vector is empty, in which case its contents will not be
	/// modified anyway.
	pub(super) fn make_mutable(&mut self)
	where
		T: Clone,
		A: Clone
	{
		if self.is_mutable() { return }

		let mut vec = Self::new_in(self.allocator().clone());
		// Safety: the vector is unique, and the iterator will always be shorter than or the same
		//  length as the fixed capacity.
		unsafe {
			vec.inner.extend_from_slice(&mut vec.len, self.as_slice().into());
		}

		// The shared reference is dropped.
		*self = vec;
	}
	
	/// Checks whether the vector is unique. The vector contents may be modified and the vector is
	/// allowed to grow in this case.
	pub(super) fn check_unique(&self) -> error::Result {
		if self.is_unique() {
			Ok(())
		} else {
			Err(Shared(()))
		}
	}
	
	/// Makes the vector unique, allowing it to grow.
	pub(super) fn make_unique(&mut self)
	where
		T: Clone,
		A: Clone
	{
		if self.is_unique() { return }
		
		let mut vec = Self::new_in(self.allocator().clone());
		// Safety: the vector is unique, and the iterator will always be shorter than or the same
		//  length as the fixed capacity.
		unsafe {
			vec.inner.extend_from_slice(&mut vec.len, self.as_slice().into());
		}
		
		// The shared reference is dropped.
		*self = vec;
	}

	pub(super) fn try_make_unique(&mut self) -> Result<(), AllocError>
	where
		T: Clone,
		A: Clone
	{
		if self.is_unique() { return Ok(()) }

		let mut vec = Self::try_new_in(self.allocator().clone())?;
		// Safety: the vector is unique, and the iterator will always be shorter than or the same
		//  length as the fixed capacity.
		unsafe {
			vec.inner.extend_from_slice(&mut vec.len, self.as_slice().into());
		}

		// The shared reference is dropped.
		*self = vec;
		Ok(())
	}

	#[track_caller]
	pub(super) fn retain_checked<F: FnMut(&T) -> bool>(&mut self, mut predicate: F) -> Result<(), Shared> {
		if self.is_mutable() {
			// Safety: `is_mutable` ensures either that the vector is unique, or
			//  that it has no contents to modify anyway.
			unsafe {
				self.inner.retain_mutable(&mut self.len, |elem| predicate(elem));
			}
			Ok(())
		} else {
			self.inner.retain_shared(&mut self.len, predicate)
		}
	}
	
	#[track_caller]
	pub(super) fn retain_internal_clone<F: FnMut(&mut T) -> bool>(&mut self, mut predicate: F)
	where
		T: Clone,
		A: Clone,
	{
		if self.is_mutable() {
			// Safety: `is_mutable` ensures either that the vector is unique, or
			//  that it has no contents to modify anyway.
			unsafe {
				self.inner.retain_mutable(&mut self.len, predicate);
			}
			return
		}

		
		let original_len = self.len();
		
		let mut filter = |mut elem| predicate(&mut elem).then_some(elem);
		let mut iter = self.iter().cloned();
		
		let Some(first_kept) = iter.find_map(&mut filter) else {
			// All elements were discarded.
			self.clear();
			return
		};
		
		let mut target = Self::new_in(self.allocator().clone());
		
		// Safety: the vectors have the same capacity. One cannot possibly have
		//  more elements than the other. The vector was just created so must be
		//  unique.
		unsafe {
			target.inner.push_unchecked(&mut target.len, first_kept);
			target.inner.extend_trusted(&mut target.len, iter.filter_map(filter));
		}
		
		// The shared reference is dropped.
		*self = target;
	}

	#[track_caller]
	pub(super) fn swap_remove_internal<E>(&mut self, index: usize, make_unique: fn(&mut Self) -> Result<(), E>) -> Result<T, E> {
		#[allow(clippy::panic)]
		#[cold]
		#[inline(never)]
		#[track_caller]
		fn assert_failed(index: usize, len: usize) -> ! {
			panic!("swap_remove index (is {index}) should be < len (is {len})");
		}

		let len = self.len();
		if index >= len {
			assert_failed(index, len);
		}

		make_unique(self)?;

		// Safety: index is checked within bounds above, and the vector is unique.
		unsafe {
			Ok(self.inner.swap_remove(index, &mut self.len))
		}
	}

	#[track_caller]
	pub(super) fn remove_internal<E>(&mut self, index: usize, make_unique: fn(&mut Self) -> Result<(), E>) -> Result<T, E> {
		#[allow(clippy::panic)]
		#[cold]
		#[inline(never)]
		#[track_caller]
		fn assert_failed(index: usize, len: usize) -> ! {
			panic!("removal index (is {index}) should be < len (is {len})");
		}

		let len = self.len();
		if index >= len {
			assert_failed(index, len);
		}

		make_unique(self)?;

		// Safety: index is checked within bounds above, and the vector is unique.
		unsafe {
			Ok(self.inner.remove(index, &mut self.len))
		}
	}

	#[track_caller]
	pub(super) fn insert_internal<E>(&mut self, index: usize, element: T, to_error: fn(T) -> E, make_unique: fn(&mut Self, T) -> Result<T, E>) -> Result<(), E> {
		#[allow(clippy::panic)]
		#[cold]
		#[inline(never)]
		#[track_caller]
		fn assert_failed(index: usize, len: usize) -> ! {
			panic!("insertion index (is {index}) should be <= len (is {len})");
		}

		let len = self.len();
		if index > len {
			assert_failed(index, len);
		}

		if self.is_full() {
			return Err(to_error(element))
		}

		let element = make_unique(self, element)?;

		// Safety: index is checked within bounds above, and the vector is unique.
		unsafe {
			self.inner.insert(index, &mut self.len, element);
		}
		Ok(())
	}
}

// Transparent reimplementation of core::iter::Copied
pub struct Copied<I>(pub I);

pub struct CopiedIter<I>(pub I);

impl<'a, I, T> IntoIterator for Copied<I>
where
	I: IntoIterator<Item = &'a T>,
	T: Copy + 'a
{
	type Item = T;
	type IntoIter = CopiedIter<I::IntoIter>;

	fn into_iter(self) -> Self::IntoIter {
		CopiedIter(self.0.into_iter())
	}
}

impl<'a, I, T> Iterator for CopiedIter<I>
where
	I: Iterator<Item = &'a T>,
	T: Copy + 'a
{
	type Item = T;

	fn next(&mut self) -> Option<T> {
		self.0.next().copied()
	}
}
