// Copyright 2025 - Strixpyrr
// SPDX-License-Identifier: Apache-2.0

use core::alloc::{AllocError, Allocator};
use crate::error;
use crate::error::{Shared, Result};
use crate::raw::RawVec;
use crate::vec::Vec;

impl<T, const ATOMIC: bool> Vec<T, ATOMIC> {
	#[track_caller]
	pub(super) unsafe fn from_iter_trusted(iter: impl IntoIterator<Item = T>, capacity: usize) -> Self {
		let mut vec = Self::with_capacity(capacity);
		vec.inner.extend_trusted(&mut vec.len, iter);
		vec
	}
}

impl<T, A: Allocator, const ATOMIC: bool> Vec<T, ATOMIC, A> {
	fn try_with_capacity_in(capacity: usize, alloc: A) -> Result<Self, AllocError> {
		Ok(Self {
			inner: RawVec::try_with_capacity(capacity, alloc)?,
			len: 0,
		})
	}
	
	fn is_mutable(&self) -> bool {
		self.is_empty() || self.is_unique()
	}

	/// Checks whether the vector contents are mutable, either empty or unique. The vector length
	/// may not be allowed to grow in this case.
	pub(super) fn check_mutable(&self) -> Result {
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

		// Todo: should the target allocate the same capacity as the source or just enough to hold
		//  its length?
		let mut vec = Self::with_capacity_in(self.capacity(), self.allocator().clone());
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
	pub(super) fn check_unique(&self) -> Result {
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

		// Todo: should the target allocate the same capacity as the source or just enough to hold
		//  its length?
		let mut vec = Self::with_capacity_in(self.capacity(), self.allocator().clone());
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

		let mut vec = Self::try_with_capacity_in(self.capacity(), self.allocator().clone())?;
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
	pub(super) fn insert_internal(&mut self, index: usize, element: T, reserve: fn(&mut Self) -> Result) -> Result {
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

		reserve(self)?;

		// Safety: index is checked within bounds above, and the vector is unique.
		//  The vector is large enough to hold the new element.
		unsafe {
			self.inner.insert(index, &mut self.len, element);
		}
		Ok(())
	}
	
	#[track_caller]
	pub(super) unsafe fn extend_internal(&mut self, iter: impl IntoIterator<Item = T>) {
		for v in iter {
			self.inner.reserve(self.len(), 1);
			// Safety: `reserve` ensures the vector is not full.
			self.inner.push_unchecked(&mut self.len, v);
		}
	}
	
	#[track_caller]
	pub(super) fn resize_internal<V>(
		&mut self,
		new_len: usize,
		extend: unsafe fn(&mut RawVec<[T], A>, &mut usize, usize, V),
		fill: V,
	) -> Result {
		if let Some(fill_len) = new_len.checked_sub(self.len()) {
			self.try_reserve(fill_len)?;
			self.check_unique()?;

			// Safety: `check_unique` ensures the vector holds a unique reference, and
			//  `fill_len` will always fit in the vector.
			unsafe {
				extend(&mut self.inner, &mut self.len, fill_len, fill);
			}

			Ok(())
		} else {
			self.truncate(new_len);
			Ok(())
		}
	}
	
	#[track_caller]
	pub(super) fn resize_clone<V>(
		&mut self,
		new_len: usize,
		extend: unsafe fn(&mut RawVec<[T], A>, &mut usize, usize, V),
		fill: V,
	) where
		T: Clone,
		A: Clone,
	{
		if let Some(fill_len) = new_len.checked_sub(self.len()) {
			self.reserve(fill_len);
			self.make_unique();

			// Safety: `make_unique` ensures the vector holds a unique reference, and
			//  `fill_len` will always fit in the vector.
			unsafe {
				extend(&mut self.inner, &mut self.len, fill_len, fill);
			}
		} else {
			self.truncate(new_len);
		}
	}
}
