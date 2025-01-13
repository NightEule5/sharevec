// Copyright 2025 - Strixpyrr
// SPDX-License-Identifier: Apache-2.0

pub(super) use crate::macros::{delegate, shared};

macro_rules! insert {
    ($expr:expr) => {
		match $expr {
			Ok(v) => Ok(v),
			Err(TryInsert::FullCapacity { element }) => Err(element),
			Err(TryInsert::Shared { .. }) => core::hint::unreachable_unchecked()
		}
	};
}

macro_rules! extend {
    ($expr:expr) => {
		match $expr {
			Ok(v) => Ok(v),
			Err(TryExtend::FullCapacity { remaining, .. }) => Err(crate::array::FullCapacity { remaining }),
			Err(TryExtend::Shared { .. }) => core::hint::unreachable_unchecked()
		}
	};
}

macro_rules! extend_iter {
    ($expr:expr) => {
		match $expr {
			Ok(v) => Ok(v),
			Err(TryExtendIter::FullCapacity { iter }) => Err(iter),
			Err(TryExtendIter::Shared { .. }) => core::hint::unreachable_unchecked()
		}
	};
}

pub(super) use {insert, extend, extend_iter};
