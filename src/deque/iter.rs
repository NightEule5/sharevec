// Copyright 2025 - Strixpyrr
// SPDX-License-Identifier: Apache-2.0

use core::{fmt, mem, slice};
use core::fmt::{Debug, Formatter};
use core::iter::FusedIterator;
#[cfg(feature = "unstable-traits")]
use core::iter::TrustedLen;
#[cfg(feature = "unstable-traits")]
use core::num::NonZero;
#[cfg(feature = "unstable-traits")]
use core::ops::Try;

pub struct Iter<'a, T: 'a> {
	a: slice::Iter<'a, T>,
	b: slice::Iter<'a, T>
}

impl<'a, T: 'a> Iter<'a, T> {
	pub(super) fn new(a: slice::Iter<'a, T>, b: slice::Iter<'a, T>) -> Self {
		Self { a, b }
	}

	/// Returns the underlying data as a pair of slices. The slices contain, in order, the contents
	/// of the deque not yet yielded by the iterator.
	pub fn as_slices(&self) -> (&'a [T], &'a [T]) {
		(self.a.as_slice(), self.b.as_slice())
	}
}

impl<T> Clone for Iter<'_, T> {
	fn clone(&self) -> Self {
		Self {
			a: self.a.clone(),
			b: self.b.clone()
		}
	}
}

impl<T: Debug> Debug for Iter<'_, T> {
	fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
		f.debug_tuple("Iter")
		 .field(&self.a.as_slice())
		 .field(&self.b.as_slice())
		 .finish()
	}
}

impl<T> Default for Iter<'_, T> {
	fn default() -> Self {
		Self::new(Default::default(), Default::default())
	}
}

impl<'a, T: 'a> Iterator for Iter<'a, T> {
	type Item = &'a T;

	fn next(&mut self) -> Option<&'a T> {
		match self.a.next() {
			Some(element) => Some(element),
			None => {
				mem::swap(&mut self.a, &mut self.b);
				self.a.next()
			}
		}
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let len = self.len();
		(len, Some(len))
	}

	fn last(mut self) -> Option<&'a T> {
		self.next_back()
	}

	#[cfg(feature = "unstable-traits")]
	fn advance_by(&mut self, n: usize) -> Result<(), NonZero<usize>> {
		match self.a.advance_by(n) {
			Ok(()) => Ok(()),
			Err(n) => {
				mem::swap(&mut self.a, &mut self.b);
				self.a.advance_by(n.get())
			}
		}
	}

	#[cfg(feature = "unstable-traits")]
	fn try_fold<B, F, R>(&mut self, init: B, mut f: F) -> R
	where
		F: FnMut(B, Self::Item) -> R,
		R: Try<Output = B>,
	{
		let accum = self.a.try_fold(init, &mut f)?;
		self.b.try_fold(accum, &mut f)
	}

	fn fold<Acc, F>(self, init: Acc, mut f: F) -> Acc
	where
		F: FnMut(Acc, Self::Item) -> Acc,
	{
		let accum = self.a.fold(init, &mut f);
		self.b.fold(accum, &mut f)
	}
}

impl<'a, T: 'a> DoubleEndedIterator for Iter<'a, T> {
	fn next_back(&mut self) -> Option<Self::Item> {
		match self.b.next_back() {
			Some(element) => Some(element),
			None => {
				mem::swap(&mut self.a, &mut self.b);
				self.b.next_back()
			}
		}
	}

	#[cfg(feature = "unstable-traits")]
	fn advance_back_by(&mut self, n: usize) -> Result<(), NonZero<usize>> {
		match self.b.advance_back_by(n) {
			Ok(()) => Ok(()),
			Err(n) => {
				mem::swap(&mut self.a, &mut self.b);
				self.b.advance_back_by(n.get())
			}
		}
	}

	#[cfg(feature = "unstable-traits")]
	fn try_rfold<B, F, R>(&mut self, init: B, mut f: F) -> R
	where
		F: FnMut(B, Self::Item) -> R,
		R: Try<Output = B>,
	{
		let accum = self.b.try_rfold(init, &mut f)?;
		self.a.try_rfold(accum, &mut f)
	}

	fn rfold<Acc, F>(self, init: Acc, mut f: F) -> Acc
	where
		F: FnMut(Acc, Self::Item) -> Acc,
	{
		let accum = self.b.rfold(init, &mut f);
		self.a.rfold(accum, &mut f)
	}
}

impl<T> ExactSizeIterator for Iter<'_, T> {
	fn len(&self) -> usize {
		self.a.len() + self.b.len()
	}

	#[cfg(feature = "unstable-traits")]
	fn is_empty(&self) -> bool {
		self.a.is_empty() && self.b.is_empty()
	}
}

#[cfg(feature = "unstable-traits")]
// Safety: this iterator always returns the number of elements given by size_hint.
unsafe impl<T> TrustedLen for Iter<'_, T> { }

impl<T> FusedIterator for Iter<'_, T> { }

pub struct IterMut<'a, T: 'a> {
	a: slice::IterMut<'a, T>,
	b: slice::IterMut<'a, T>
}

impl<'a, T: 'a> IterMut<'a, T> {
	pub(super) fn new(a: slice::IterMut<'a, T>, b: slice::IterMut<'a, T>) -> Self {
		Self { a, b }
	}

	/// Consumes the iterator, returning the underlying data as a pair of mutable slices. The slices
	/// contain, in order, the contents of the deque not yet yielded by the iterator.
	///
	/// The returned slices are borrowed for as long as the original lifetime.
	pub fn into_slices(self) -> (&'a mut [T], &'a mut [T]) {
		(self.a.into_slice(), self.b.into_slice())
	}

	/// Returns the underlying data as a pair of slices. The slices contain, in order, the
	/// contents of the deque not yet yielded by the iterator.
	pub fn as_slices(&self) -> (&[T], &[T]) {
		(self.a.as_slice(), self.b.as_slice())
	}

	// Todo: requires unstable feature
	/*pub fn as_mut_slices(&mut self) -> (&mut [T], &mut [T]) {
		(self.a.as_mut_slice(), self.b.as_mut_slice())
	}*/
}

impl<T> Default for IterMut<'_, T> {
	fn default() -> Self {
		Self::new(Default::default(), Default::default())
	}
}

impl<T: Debug> Debug for IterMut<'_, T> {
	fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
		f.debug_tuple("IterMut")
		 .field(&self.a.as_slice())
		 .field(&self.b.as_slice())
		 .finish()
	}
}

impl<'a, T: 'a> Iterator for IterMut<'a, T> {
	type Item = &'a mut T;

	fn next(&mut self) -> Option<&'a mut T> {
		match self.a.next() {
			Some(elem) => Some(elem),
			None => {
				mem::swap(&mut self.a, &mut self.b);
				self.a.next()
			}
		}
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let len = self.len();
		(len, Some(len))
	}

	fn last(mut self) -> Option<&'a mut T> {
		self.next_back()
	}

	#[cfg(feature = "unstable-traits")]
	fn advance_by(&mut self, n: usize) -> Result<(), NonZero<usize>> {
		match self.a.advance_by(n) {
			Ok(()) => Ok(()),
			Err(remaining) => {
				mem::swap(&mut self.a, &mut self.b);
				self.a.advance_by(remaining.get())
			}
		}
	}

	#[cfg(feature = "unstable-traits")]
	fn try_fold<B, F, R>(&mut self, init: B, mut f: F) -> R
	where
		F: FnMut(B, Self::Item) -> R,
		R: Try<Output = B>,
	{
		let accum = self.a.try_fold(init, &mut f)?;
		self.b.try_fold(accum, &mut f)
	}

	fn fold<Acc, F>(self, init: Acc, mut f: F) -> Acc
	where
		F: FnMut(Acc, Self::Item) -> Acc,
	{
		let accum = self.a.fold(init, &mut f);
		self.b.fold(accum, &mut f)
	}
}

impl<'a, T: 'a> DoubleEndedIterator for IterMut<'a, T> {
	fn next_back(&mut self) -> Option<Self::Item> {
		match self.b.next() {
			Some(elem) => Some(elem),
			None => {
				mem::swap(&mut self.a, &mut self.b);
				self.b.next_back()
			}
		}
	}

	#[cfg(feature = "unstable-traits")]
	fn advance_back_by(&mut self, n: usize) -> Result<(), NonZero<usize>> {
		match self.b.advance_by(n) {
			Ok(()) => Ok(()),
			Err(remaining) => {
				mem::swap(&mut self.a, &mut self.b);
				self.b.advance_back_by(remaining.get())
			}
		}
	}

	#[cfg(feature = "unstable-traits")]
	fn try_rfold<B, F, R>(&mut self, init: B, mut f: F) -> R
	where
		F: FnMut(B, Self::Item) -> R,
		R: Try<Output = B>,
	{
		let accum = self.b.try_rfold(init, &mut f)?;
		self.a.try_rfold(accum, &mut f)
	}

	fn rfold<Acc, F>(self, init: Acc, mut f: F) -> Acc
	where
		F: FnMut(Acc, Self::Item) -> Acc,
	{
		let accum = self.b.rfold(init, &mut f);
		self.a.rfold(accum, &mut f)
	}
}

impl<'a, T: 'a> ExactSizeIterator for IterMut<'a, T> {
	fn len(&self) -> usize {
		self.a.len() + self.b.len()
	}

	#[cfg(feature = "unstable-traits")]
	fn is_empty(&self) -> bool {
		self.a.is_empty() && self.b.is_empty()
	}
}

#[cfg(feature = "unstable-traits")]
// Safety: this iterator always returns the number of elements given by size_hint.
unsafe impl<T> TrustedLen for IterMut<'_, T> { }

impl<T> FusedIterator for IterMut<'_, T> { }
