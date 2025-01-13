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
use super::ArrayVec;
	
pub struct Drain<'a, T: 'a, const N: usize, A: Allocator + 'a, const ATOMIC: bool> {
	_ref: PhantomData<&'a mut ArrayVec<T, N, ATOMIC, A>>,
}
	
impl<T: fmt::Debug, const N: usize, A: Allocator, const ATOMIC: bool> fmt::Debug for Drain<'_, T, N, A, ATOMIC> {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		todo!()
	}
}
	
impl<T, const N: usize, A: Allocator, const ATOMIC: bool> Drain<'_, T, N, A, ATOMIC> {
	/// Returns the remaining elements as a slice.
	#[must_use]
	pub fn as_slice(&self) -> &[T] {
		todo!()
	}
	
	/// Returns a reference to the underlying allocator.
	#[must_use]
	pub fn allocator(&self) -> &A {
		todo!()
	}
	
	/// Keeps unyielded elements in the source vector.
	pub fn keep_rest(self) {
		todo!()
	}
}
	
impl<T, const N: usize, A: Allocator, const ATOMIC: bool> AsRef<[T]> for Drain<'_, T, N, A, ATOMIC> {
	fn as_ref(&self) -> &[T] {
		self.as_slice()
	}
}
	
impl<T, const N: usize, A: Allocator, const ATOMIC: bool> Iterator for Drain<'_, T, N, A, ATOMIC> {
	type Item = T;
	
	fn next(&mut self) -> Option<Self::Item> {
		todo!()
	}
	
	fn size_hint(&self) -> (usize, Option<usize>) {
		let len = self.len();
		(len, Some(len))
	}
}
	
impl<T, const N: usize, A: Allocator, const ATOMIC: bool> DoubleEndedIterator for Drain<'_, T, N, A, ATOMIC> {
	fn next_back(&mut self) -> Option<Self::Item> {
		todo!()
	}
	
	#[cfg(feature = "unstable-traits")]
	fn advance_back_by(&mut self, n: usize) -> Result<(), NonZero<usize>> {
		todo!()
	}
}
	
impl<T, const N: usize, A: Allocator, const ATOMIC: bool> Drop for Drain<'_, T, N, A, ATOMIC> {
	fn drop(&mut self) {
		todo!()
	}
}
	
impl<T, const N: usize, A: Allocator, const ATOMIC: bool> ExactSizeIterator for Drain<'_, T, N, A, ATOMIC> {
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
unsafe impl<T, const N: usize, A: Allocator, const ATOMIC: bool> TrustedLen for Drain<'_, T, N, A, ATOMIC> { }
	
impl<T, const N: usize, A: Allocator, const ATOMIC: bool> FusedIterator for Drain<'_, T, N, A, ATOMIC> { }
