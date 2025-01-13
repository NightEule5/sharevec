// Copyright 2024 - Strixpyrr
// SPDX-License-Identifier: Apache-2.0

use core::fmt::{self, Debug, Display, Formatter};

pub type Result<T = (), E = Shared> = core::result::Result<T, E>;

#[derive(Eq, PartialEq)] // For tests
pub struct Shared<E = ()>(pub E);

impl Copy for Shared { }
impl Clone for Shared {
	#[inline(always)] fn clone(&self) -> Self { *self }
}

// Hide the contained element
impl<E> Debug for Shared<E> {
	fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
		f.write_str("Shared")
	}
}

impl<E> Display for Shared<E> {
	fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
		f.write_str("vector has a shared underlying allocation which cannot be modified")
	}
}

#[cfg(feature = "std")]
impl<E> std::error::Error for Shared<E> { }
