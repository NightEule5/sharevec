// Copyright 2025 - Strixpyrr
// SPDX-License-Identifier: Apache-2.0

use core::alloc::Allocator;
use core::iter::FusedIterator;
#[cfg(feature = "unstable-traits")]
use core::iter::TrustedLen;
use core::marker::PhantomData;
use core::num::NonZero;
#[cfg(feature = "unstable-traits")]
use core::ops::Try;

pub struct IntoIter<T, A: Allocator, const ATOMIC: bool> {
	_t: PhantomData<T>,
	_a: PhantomData<A>,
}

impl<T, A: Allocator, const ATOMIC: bool> Iterator for IntoIter<T, A, ATOMIC> {
	type Item = T;

	fn next(&mut self) -> Option<Self::Item> {
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

	fn last(self) -> Option<Self::Item> {
		todo!("pop_back")
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

impl<T, A: Allocator, const ATOMIC: bool> DoubleEndedIterator for IntoIter<T, A, ATOMIC> {
	fn next_back(&mut self) -> Option<Self::Item> {
		todo!()
	}

	#[cfg(feature = "unstable-traits")]
	fn advance_back_by(&mut self, n: usize) -> Result<(), NonZero<usize>> {
		todo!()
	}

	#[cfg(feature = "unstable-traits")]
	fn try_rfold<B, F, R>(&mut self, mut init: B, mut f: F) -> R
	where
		F: FnMut(B, Self::Item) -> R,
		R: Try<Output = B>,
	{
		todo!()
	}

	fn rfold<B, F>(self, init: B, f: F) -> B
	where
		Self: Sized,
		F: FnMut(B, Self::Item) -> B,
	{
		todo!()
	}
}

impl<T, A: Allocator, const ATOMIC: bool> ExactSizeIterator for IntoIter<T, A, ATOMIC> {
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
unsafe impl<T, A: Allocator, const ATOMIC: bool> TrustedLen for IntoIter<T, A, ATOMIC> { }

impl<T, A: Allocator, const ATOMIC: bool> FusedIterator for IntoIter<T, A, ATOMIC> { }

impl<T: Clone, A: Allocator + Clone, const ATOMIC: bool> Clone for IntoIter<T, A, ATOMIC> {
	fn clone(&self) -> Self {
		todo!()
	}
}

impl<T, A: Allocator, const ATOMIC: bool> Drop for IntoIter<T, A, ATOMIC> {
	fn drop(&mut self) {
		todo!()
	}
}
