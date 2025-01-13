// Copyright 2025 - Strixpyrr
// SPDX-License-Identifier: Apache-2.0

macro_rules! delegate {
    ($self:ident.$fallible:ident($($args:expr),*) -> $unwrap:ident$(<$err_type:ident>)?) => {
		// Safety: this type already upholds uniqueness as an invariant
		unsafe {
			$unwrap!($self.as_inner_mut().$fallible($($args),*)$(; $err_type)?)
		}
	};
    (mut $self:ident.$infallible:ident($($args:expr),*)) => {
		$self.as_inner_mut().$infallible($($args),*)
	};
    ($self:ident.$infallible:ident($($args:expr),*)) => {
		$self.as_inner().$infallible($($args),*)
	};
}

macro_rules! shared {
    ($expr:expr) => {
		$expr.unwrap_unchecked()
	};
}

pub(crate) use {delegate, shared};
