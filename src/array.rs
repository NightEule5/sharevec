// Copyright 2025 - Strixpyrr
// SPDX-License-Identifier: Apache-2.0

#[cfg(feature = "array-deque")]
pub mod deque;
#[cfg(feature = "array-vec")]
pub mod vec;
mod macros;

use core::fmt;
use crate::error::Shared;

pub struct TryFromSlice<const N: usize>(usize);

impl<const N: usize> TryFromSlice<N> {
	/// The length of the slice.
	pub fn len(&self) -> usize {
		self.0
	}
	/// The number of elements over the capacity.
	pub fn remainder(&self) -> usize {
		self.len() - N
	}
}

/// An error on insertion or push, indicating either the vector being full or shared.
#[derive(PartialEq, Eq)]
#[non_exhaustive]
pub enum TryInsert<T> {
	/// The vector's fixed capacity has been filled.
	FullCapacity {
		/// The element that could not be inserted or pushed.
		element: T
	},
	/// The vector holds a shared reference to its buffer, and cannot be modified.
	Shared {
		/// The element that could not be inserted or pushed.
		element: T
	},
}

impl<T> TryInsert<T> {
	/// Returns the element that could not be inserted or pushed.
	pub fn into_element(self) -> T {
		let (Self::FullCapacity { element } |
			 Self::Shared       { element }) = self;
		element
	}
	/// Returns a reference to the element that could not be inserted or pushed.
	pub fn element(&self) -> &T {
		let (Self::FullCapacity { element } |
			 Self::Shared       { element }) = self;
		element
	}
}

impl<T> fmt::Debug for TryInsert<T> {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		f.debug_struct(match self {
			TryInsert::FullCapacity { .. } => "FullCapacity",
			TryInsert::Shared { .. } => "Shared",
		}).finish_non_exhaustive()
	}
}

impl<T> fmt::Display for TryInsert<T> {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		f.write_str(match self {
			Self::FullCapacity { .. } =>
				"element could not be inserted: the fixed vector capacity was full",
			Self::Shared { .. } =>
				"element could not be inserted: the vector held a shared reference \
				and could not be modified"
		})
	}
}

impl<T> From<Shared<T>> for TryInsert<T> {
	fn from(Shared(element): Shared<T>) -> Self {
		Self::Shared { element }
	}
}

#[cfg(feature = "std")]
impl<T> std::error::Error for TryInsert<T> { }

/// An error on extending, indicating either the vector being full or shared.
#[non_exhaustive]
#[derive(Eq, PartialEq)] // For tests
pub enum TryExtend {
	/// The vector's fixed capacity has been filled.
	FullCapacity {
		/// The number of elements that could not be appended.
		remaining: usize,
	},
	/// The vector holds a shared reference to its buffer, and cannot be modified.
	Shared,
}

impl fmt::Debug for TryExtend {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		match self {
			Self::FullCapacity { remaining } =>
				f.debug_struct("FullCapacity")
				 .field("remaining", remaining)
				 .finish(),
			Self::Shared => f.write_str("Shared")
		}
	}
}

impl fmt::Display for TryExtend {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		match self {
			&Self::FullCapacity { remaining } => fmt::Display::fmt(&FullCapacity { remaining }, f),
			Self::Shared => f.write_str(
				"could not extend the vector: the vector held a shared reference \
				and could not be modified"
			)
		}
	}
}

impl From<Shared> for TryExtend {
	fn from(_: Shared) -> Self {
		Self::Shared
	}
}

impl From<FullCapacity> for TryExtend {
	fn from(FullCapacity { remaining }: FullCapacity) -> Self {
		Self::FullCapacity { remaining }
	}
}

#[cfg(feature = "std")]
impl std::error::Error for TryExtend { }

/// An error on extending, indicating either the vector being full or shared.
#[non_exhaustive]
pub enum TryExtendIter<T: IntoIterator> {
	/// The vector's fixed capacity has been filled.
	FullCapacity {
		first: Option<T::Item>,
		iter: T::IntoIter
	},
	/// The vector holds a shared reference to its buffer, and cannot be modified.
	Shared {
		iter: T
	},
}

// For tests
impl<T: IntoIterator> Eq for TryExtendIter<T> { }
impl<T: IntoIterator> PartialEq for TryExtendIter<T> {
	fn eq(&self, other: &Self) -> bool {
		matches!(
			(self, other),
			(Self::FullCapacity { .. }, Self::FullCapacity { .. }) |
			(Self::Shared { .. }, Self::Shared { .. })
		)
	}
}

impl<T: IntoIterator> fmt::Debug for TryExtendIter<T> {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		match self {
			Self::FullCapacity { .. } =>
				f.debug_struct("FullCapacity")
				 .finish_non_exhaustive(),
			Self::Shared { .. } =>
				f.debug_struct("Shared")
				 .finish_non_exhaustive()
		}
	}
}

impl<T: IntoIterator> fmt::Display for TryExtendIter<T> {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		match self {
			&Self::FullCapacity { .. } =>
				f.write_str(
					"could not extend the vector: no spare capacity remaining"
				),
			Self::Shared { .. } => f.write_str(
				"could not extend the vector: the vector held a shared reference \
				and could not be modified"
			)
		}
	}
}

#[cfg(feature = "std")]
impl<T: IntoIterator> std::error::Error for TryExtendIter<T> { }

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct FullCapacity {
	/// The number of elements that could not be appended.
	pub remaining: usize
}

impl fmt::Display for FullCapacity {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		write!(f, "could not extend the vector: no spare capacity remaining for {} elements", self.remaining)
	}
}
