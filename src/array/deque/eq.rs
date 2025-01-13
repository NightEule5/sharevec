// Copyright 2025 - Strixpyrr
// SPDX-License-Identifier: Apache-2.0

use core::alloc::Allocator;
use super::{ArrayDeque, Unique};

macro_rules! gen_eq {
	() => { };
	($lhs:ty, $rhs:ty;$($next:tt)*) => {
		gen_eq! { $lhs, $rhs [A: Allocator, const ATOMIC: bool];$($next)* }
	};
    ($lhs:ty, $rhs:ty [$($params:tt)+];$($next:tt)*) => {
		impl<T: PartialEq<U>, U, const N: usize, $($params)+> PartialEq<$rhs> for $lhs {
			fn eq(&self, other: &$rhs) -> bool {
				todo!()
			}
		}
		gen_eq! { $($next)* }
	};
}

macro_rules! gen_const_eq {
    ($($lhs:ty, $rhs:ty;)+) => {
		$(
		impl<T: PartialEq<U>, U, const N: usize, const O: usize, A: Allocator, const ATOMIC: bool> PartialEq<$rhs> for $lhs {
			fn eq(&self, other: &$rhs) -> bool {
				todo!()
			}
		}
		)+
	};
}

gen_eq! {
	ArrayDeque<T, N, ATOMIC1, A1>, ArrayDeque<U, O, ATOMIC2, A2> [const O: usize, A1: Allocator, A2: Allocator, const ATOMIC1: bool, const ATOMIC2: bool];
	ArrayDeque<T, N, ATOMIC, A>, &[U];
	ArrayDeque<T, N, ATOMIC, A>, &mut [U];
	&[T], ArrayDeque<U, N, ATOMIC, A>;
	&mut [T], ArrayDeque<U, N, ATOMIC, A>;
	ArrayDeque<T, N, ATOMIC, A>, [U];
	[T], ArrayDeque<U, N, ATOMIC, A>;
	Unique<'_, T, N, A1, ATOMIC1>, Unique<'_, U, O, A2, ATOMIC2> [const O: usize, A1: Allocator, A2: Allocator, const ATOMIC1: bool, const ATOMIC2: bool];
	Unique<'_, T, N, A1, ATOMIC1>, ArrayDeque<U, O, ATOMIC2, A2> [const O: usize, A1: Allocator, A2: Allocator, const ATOMIC1: bool, const ATOMIC2: bool];
	ArrayDeque<T, N, ATOMIC1, A1>, Unique<'_, U, O, A2, ATOMIC2> [const O: usize, A1: Allocator, A2: Allocator, const ATOMIC1: bool, const ATOMIC2: bool];
	Unique<'_, T, N, A, ATOMIC>, &[U];
	Unique<'_, T, N, A, ATOMIC>, &mut [U];
	&[T], Unique<'_, U, N, A, ATOMIC>;
	&mut [T], Unique<'_, U, N, A, ATOMIC>;
	Unique<'_, T, N, A, ATOMIC>, [U];
	[T], Unique<'_, U, N, A, ATOMIC>;
}

gen_const_eq! {
	ArrayDeque<T, N, ATOMIC, A>, [U; O];
	ArrayDeque<T, N, ATOMIC, A>, &[U; O];
	ArrayDeque<T, N, ATOMIC, A>, &mut [U; O];
	[T; O], ArrayDeque<U, N, ATOMIC, A>;
	&[T; O], ArrayDeque<U, N, ATOMIC, A>;
	&mut [T; O], ArrayDeque<U, N, ATOMIC, A>;
	Unique<'_, T, N, A, ATOMIC>, [U; O];
	Unique<'_, T, N, A, ATOMIC>, &[U; O];
	Unique<'_, T, N, A, ATOMIC>, &mut [U; O];
	[T; O], Unique<'_, U, N, A, ATOMIC>;
	&[T; O], Unique<'_, U, N, A, ATOMIC>;
	&mut [T; O], Unique<'_, U, N, A, ATOMIC>;
}
