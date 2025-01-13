// Copyright 2025 - Strixpyrr
// SPDX-License-Identifier: Apache-2.0

use core::alloc::Allocator;
use core::fmt;
use core::iter::FusedIterator;
#[cfg(feature = "unstable-traits")]
use core::iter::TrustedLen;
use core::marker::PhantomData;
#[cfg(feature = "unstable-traits")]
use core::num::NonZero;
#[cfg(feature = "unstable-traits")]
use core::ops::Try;
use crate::error::Shared;

pub struct IntoIter<T, const N: usize, A: Allocator, const ATOMIC: bool> {
	_t: PhantomData<T>,
	_a: PhantomData<A>,
}
	
impl<T: fmt::Debug, const N: usize, A: Allocator, const ATOMIC: bool> fmt::Debug for IntoIter<T, N, A, ATOMIC> {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		todo!()
	}
}
	
impl<T, const N: usize, A: Allocator, const ATOMIC: bool> IntoIter<T, N, A, ATOMIC> {
	/// Returns the remaining elements as a slice.
	pub fn as_slice(&self) -> &[T] {
		todo!()
	}
		
	/// Returns the remaining elements as a mutable slice, if the source vector is not shared.
	///
	/// # Errors
	///
	/// Returns an error if the vector holds a shared reference to its buffer.
	pub fn try_as_mut_slice(&mut self) -> Result<&mut [T], Shared> {
		todo!()
	}
		
	/// Returns a reference to the underlying allocator.
	pub fn allocator(&self) -> &A {
		todo!()
	}
}
	
impl<T, const N: usize, A: Allocator, const ATOMIC: bool> AsRef<[T]> for IntoIter<T, N, A, ATOMIC> {
	fn as_ref(&self) -> &[T] {
		self.as_slice()
	}
}
	
impl<T, const N: usize, A: Allocator, const ATOMIC: bool> Iterator for IntoIter<T, N, A, ATOMIC> {
	type Item = T;
		
	fn next(&mut self) -> Option<T> {
		todo!()
	}
	
	#[cfg(feature = "unstable-traits")]
	fn next_chunk<const CHUNK: usize>(&mut self) -> Result<[T; CHUNK], core::array::IntoIter<T, CHUNK>> {
		todo!()
	}
	
	fn size_hint(&self) -> (usize, Option<usize>) {
		todo!()
	}
	
	fn count(self) -> usize {
		self.len()
	}
	
	#[cfg(feature = "unstable-traits")]
	fn advance_by(&mut self, n: usize) -> Result<(), NonZero<usize>> {
		todo!()
	}
	
	#[cfg(feature = "unstable-traits")]
	fn try_fold<B, F, R>(&mut self, init: B, f: F) -> R
	where
		Self: Sized,
		F: FnMut(B, Self::Item) -> R,
		R: Try<Output = B>,
	{
		todo!()
	}
	
	fn fold<B, F>(self, init: B, f: F) -> B
	where
		F: FnMut(B, Self::Item) -> B,
	{
		todo!()
	}
}
	
impl<T, const N: usize, A: Allocator, const ATOMIC: bool> DoubleEndedIterator for IntoIter<T, N, A, ATOMIC> {
	fn next_back(&mut self) -> Option<Self::Item> {
		todo!()
	}
	
	#[cfg(feature = "unstable-traits")]
	fn advance_back_by(&mut self, n: usize) -> Result<(), NonZero<usize>> {
		todo!()
	}
}
	
impl<T, const N: usize, A: Allocator, const ATOMIC: bool> ExactSizeIterator for IntoIter<T, N, A, ATOMIC> {
	fn len(&self) -> usize {
		todo!()
	}
		
	#[cfg(feature = "unstable-traits")]
	fn is_empty(&self) -> bool {
		todo!()
	}
}
	
#[cfg(feature = "unstable-traits")]
// Safety: this iterator always returns the number of elements given by size_hint.
unsafe impl<T, const N: usize, A: Allocator, const ATOMIC: bool> TrustedLen for IntoIter<T, N, A, ATOMIC> { }
	
impl<T, const N: usize, A: Allocator, const ATOMIC: bool> FusedIterator for IntoIter<T, N, A, ATOMIC> { }
	
impl<T: Clone, const N: usize, A: Allocator + Clone, const ATOMIC: bool> Clone for IntoIter<T, N, A, ATOMIC> {
	fn clone(&self) -> Self {
		todo!()
	}
}
	
impl<T, const N: usize, A: Allocator, const ATOMIC: bool> Drop for IntoIter<T, N, A, ATOMIC> {
	fn drop(&mut self) {
		todo!()
	}
}
