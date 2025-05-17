// Copyright 2025 - Strixpyrr
// SPDX-License-Identifier: Apache-2.0

use core::alloc::Allocator;
#[cfg(feature = "array-deque")]
use crate::array::deque::{
	ArrayDeque,
	unique::Unique as ArrayDequeUnique
};
#[cfg(feature = "array-vec")]
use crate::array::vec::{
	ArrayVec,
	unique::Unique as ArrayVecUnique
};
#[cfg(feature = "deque")]
use crate::deque::{
	Deque,
	unique::Unique as DequeUnique
};
#[cfg(feature = "vec")]
use crate::vec::{
	Vec,
	unique::Unique as VecUnique
};

/// A marker for any reference-counted vector type in this crate.
pub trait RcVector<T, A: Allocator, const ATOMIC: bool>: private::Vec<T> { }
/// A marker for any unique wrapper type in this crate.
pub trait UniqueVector<T, A: Allocator, const ATOMIC: bool>: RcVector<T, A, ATOMIC> { }

#[cfg(feature = "array-vec")]
impl<T, const N: usize, A: Allocator, const ATOMIC: bool> RcVector<T, A, ATOMIC> for ArrayVec<T, N, ATOMIC, A> { }
#[cfg(feature = "array-vec")]
impl<T, const N: usize, A: Allocator, const ATOMIC: bool> RcVector<T, A, ATOMIC> for ArrayVecUnique<'_, T, N, A, ATOMIC> { }
#[cfg(feature = "array-deque")]
impl<T, const N: usize, A: Allocator, const ATOMIC: bool> RcVector<T, A, ATOMIC> for ArrayDeque<T, N, ATOMIC, A> { }
#[cfg(feature = "array-deque")]
impl<T, const N: usize, A: Allocator, const ATOMIC: bool> RcVector<T, A, ATOMIC> for ArrayDequeUnique<'_, T, N, A, ATOMIC> { }
#[cfg(feature = "vec")]
impl<T, A: Allocator, const ATOMIC: bool> RcVector<T, A, ATOMIC> for Vec<T, ATOMIC, A> { }
#[cfg(feature = "vec")]
impl<T, A: Allocator, const ATOMIC: bool> RcVector<T, A, ATOMIC> for VecUnique<'_, T, A, ATOMIC> { }
#[cfg(feature = "deque")]
impl<T, A: Allocator, const ATOMIC: bool> RcVector<T, A, ATOMIC> for Deque<T, ATOMIC, A> { }
#[cfg(feature = "deque")]
impl<T, A: Allocator, const ATOMIC: bool> RcVector<T, A, ATOMIC> for DequeUnique<'_, T, A, ATOMIC> { }

#[cfg(feature = "array-vec")]
impl<T, const N: usize, A: Allocator, const ATOMIC: bool> UniqueVector<T, A, ATOMIC> for ArrayVecUnique<'_, T, N, A, ATOMIC> { }
#[cfg(feature = "array-deque")]
impl<T, const N: usize, A: Allocator, const ATOMIC: bool> UniqueVector<T, A, ATOMIC> for ArrayDequeUnique<'_, T, N, A, ATOMIC> { }
#[cfg(feature = "vec")]
impl<T, A: Allocator, const ATOMIC: bool> UniqueVector<T, A, ATOMIC> for VecUnique<'_, T, A, ATOMIC> { }
#[cfg(feature = "deque")]
impl<T, A: Allocator, const ATOMIC: bool> UniqueVector<T, A, ATOMIC> for DequeUnique<'_, T, A, ATOMIC> { }

pub(crate) mod private {
	use core::alloc::Allocator;
	use core::array;
	use crate::raw::{DequeInner, RawCollection, RawDeque, RawVec, Store, VecInner};

	fn single_slice<T>(slice: &[T]) -> array::IntoIter<&[T], 2> {
		let mut iter = [slice, &[]].into_iter();
		iter.next_back();
		iter
	}
	
	pub trait Vec<T> {
		type Inner;
		type Store: ?Sized + Store;
		type Alloc: Allocator;
		
		fn inner(&mut self) -> &mut RawCollection<Self::Store, Self::Inner, Self::Alloc>;
		
		fn is_shared(&self) -> bool;
		fn len(&self) -> usize;
		fn is_empty(&self) -> bool;
		fn slices(&self) -> array::IntoIter<&[T], 2>;
		
		fn as_ptr(&self) -> *const T;
		unsafe fn set_len(&mut self, new_len: usize);
		fn clear(&mut self);
	}

	#[cfg(feature = "array-vec")]
	impl<T, const N: usize, A: Allocator, const ATOMIC: bool> Vec<T> for super::ArrayVec<T, N, ATOMIC, A> {
		type Inner = VecInner;
		type Store = [T; N];
		type Alloc = A;

		fn inner(&mut self) -> &mut RawVec<[T; N], A> { &mut self.inner }
		
		fn is_shared(&self) -> bool {
			self.is_shared()
		}

		fn len(&self) -> usize {
			self.len()
		}
		
		fn is_empty(&self) -> bool { self.is_empty() }

		fn slices(&self) -> array::IntoIter<&[T], 2> {
			single_slice(self.as_slice())
		}

		fn as_ptr(&self) -> *const T {
			self.as_ptr()
		}

		unsafe fn set_len(&mut self, new_len: usize) {
			self.set_len(new_len);
		}

		fn clear(&mut self) {
			self.clear()
		}
	}
	
	#[cfg(feature = "array-vec")]
	impl<T, const N: usize, A: Allocator, const ATOMIC: bool> Vec<T> for super::ArrayVecUnique<'_, T, N, A, ATOMIC> {
		type Inner = VecInner;
		type Store = [T; N];
		type Alloc = A;

		fn inner(&mut self) -> &mut RawVec<[T; N], A> { &mut self.as_inner_mut().inner }
		
		fn is_shared(&self) -> bool { false }

		fn len(&self) -> usize {
			self.len()
		}

		fn is_empty(&self) -> bool { self.is_empty() }

		fn slices(&self) -> array::IntoIter<&[T], 2> {
			single_slice(self.as_slice())
		}

		fn as_ptr(&self) -> *const T {
			self.as_ptr()
		}

		unsafe fn set_len(&mut self, new_len: usize) {
			self.set_len(new_len);
		}

		fn clear(&mut self) {
			self.clear()
		}
	}
	
	#[cfg(feature = "array-deque")]
	impl<T, const N: usize, A: Allocator, const ATOMIC: bool> Vec<T> for super::ArrayDeque<T, N, ATOMIC, A> {
		type Inner = DequeInner;
		type Store = [T; N];
		type Alloc = A;

		fn inner(&mut self) -> &mut RawDeque<[T; N], A> { &mut self.inner }
		
		fn is_shared(&self) -> bool {
			self.is_shared()
		}

		fn len(&self) -> usize {
			self.len()
		}

		fn is_empty(&self) -> bool { self.is_empty() }

		fn slices(&self) -> array::IntoIter<&[T], 2> {
			Into::<[_; 2]>::into(self.as_slices()).into_iter()
		}

		fn as_ptr(&self) -> *const T {
			self.as_ptr()
		}

		unsafe fn set_len(&mut self, new_len: usize) {
			todo!()
		}

		fn clear(&mut self) {
			self.clear()
		}
	}
	
	#[cfg(feature = "array-deque")]
	impl<T, const N: usize, A: Allocator, const ATOMIC: bool> Vec<T> for super::ArrayDequeUnique<'_, T, N, A, ATOMIC> {
		type Inner = DequeInner;
		type Store = [T; N];
		type Alloc = A;

		fn inner(&mut self) -> &mut RawDeque<[T; N], A> { &mut self.as_inner_mut().inner }
		
		fn is_shared(&self) -> bool { false }

		fn len(&self) -> usize {
			self.len()
		}

		fn is_empty(&self) -> bool { self.is_empty() }

		fn slices(&self) -> array::IntoIter<&[T], 2> {
			Into::<[_; 2]>::into(self.as_slices()).into_iter()
		}

		fn as_ptr(&self) -> *const T {
			self.as_ptr()
		}

		unsafe fn set_len(&mut self, new_len: usize) {
			todo!()
		}

		fn clear(&mut self) {
			self.clear()
		}
	}
	
	#[cfg(feature = "vec")]
	impl<T, A: Allocator, const ATOMIC: bool> Vec<T> for super::Vec<T, ATOMIC, A> {
		type Inner = VecInner;
		type Store = [T];
		type Alloc = A;

		fn inner(&mut self) -> &mut RawVec<[T], A> { &mut self.inner }

		fn is_shared(&self) -> bool {
			self.is_shared()
		}

		fn len(&self) -> usize {
			self.len()
		}

		fn is_empty(&self) -> bool { self.is_empty() }

		fn slices(&self) -> array::IntoIter<&[T], 2> {
			single_slice(self.as_slice())
		}

		fn as_ptr(&self) -> *const T {
			self.as_ptr()
		}

		unsafe fn set_len(&mut self, new_len: usize) {
			self.set_len(new_len);
		}

		fn clear(&mut self) {
			self.clear()
		}
	}
	
	#[cfg(feature = "vec")]
	impl<T, A: Allocator, const ATOMIC: bool> Vec<T> for super::VecUnique<'_, T, A, ATOMIC> {
		type Inner = VecInner;
		type Store = [T];
		type Alloc = A;

		fn inner(&mut self) -> &mut RawVec<[T], A> { todo!() }

		fn is_shared(&self) -> bool { false }

		fn len(&self) -> usize {
			self.len()
		}

		fn is_empty(&self) -> bool { self.is_empty() }

		fn slices(&self) -> array::IntoIter<&[T], 2> {
			single_slice(self.as_slice())
		}

		fn as_ptr(&self) -> *const T {
			self.as_ptr()
		}

		unsafe fn set_len(&mut self, new_len: usize) {
			self.set_len(new_len);
		}

		fn clear(&mut self) {
			self.clear()
		}
	}
	
	#[cfg(feature = "deque")]
	impl<T, A: Allocator, const ATOMIC: bool> Vec<T> for super::Deque<T, ATOMIC, A> {
		type Inner = DequeInner;
		type Store = [T];
		type Alloc = A;

		fn inner(&mut self) -> &mut RawDeque<[T], A> { &mut self.inner }

		fn is_shared(&self) -> bool {
			self.is_shared()
		}

		fn len(&self) -> usize {
			self.len()
		}

		fn is_empty(&self) -> bool { self.is_empty() }

		fn slices(&self) -> array::IntoIter<&[T], 2> {
			Into::<[_; 2]>::into(self.as_slices()).into_iter()
		}

		fn as_ptr(&self) -> *const T {
			self.as_ptr()
		}

		unsafe fn set_len(&mut self, new_len: usize) {
			todo!()
		}

		fn clear(&mut self) {
			self.clear()
		}
	}
	
	#[cfg(feature = "deque")]
	impl<T, A: Allocator, const ATOMIC: bool> Vec<T> for super::DequeUnique<'_, T, A, ATOMIC> {
		type Inner = DequeInner;
		type Store = [T];
		type Alloc = A;

		fn inner(&mut self) -> &mut RawDeque<[T], A> { todo!() }

		fn is_shared(&self) -> bool { false }

		fn len(&self) -> usize {
			self.len()
		}

		fn is_empty(&self) -> bool { self.is_empty() }

		fn slices(&self) -> array::IntoIter<&[T], 2> {
			Into::<[_; 2]>::into(self.as_slices()).into_iter()
		}

		fn as_ptr(&self) -> *const T {
			self.as_ptr()
		}

		unsafe fn set_len(&mut self, new_len: usize) {
			todo!()
		}

		fn clear(&mut self) {
			self.clear()
		}
	}
}
