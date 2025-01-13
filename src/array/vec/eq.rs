// Copyright 2025 - Strixpyrr
// SPDX-License-Identifier: Apache-2.0

use core::alloc::Allocator;
use super::{ArrayVec, Unique};

macro_rules! gen_eq {
	() => { };
	($lhs:ty, $rhs:ty;$($next:tt)*) => {
		gen_eq! { $lhs, $rhs [A: Allocator, const ATOMIC: bool];$($next)* }
	};
	($lhs:ty, $rhs:ty [$($params:tt)+];$($next:tt)*) => {
		impl<T: PartialEq<U>, U, const N: usize, $($params)+> PartialEq<$rhs> for $lhs {
			fn eq(&self, other: &$rhs) -> bool { self[..] == other[..] }
		}
		gen_eq! { $($next)* }
	};
}

macro_rules! gen_const_eq {
	($($lhs:ty, $rhs:ty;)+) => {
		$(
		impl<T: PartialEq<U>, U, const N: usize, const O: usize, A: Allocator, const ATOMIC: bool> PartialEq<$rhs> for $lhs {
			fn eq(&self, other: &$rhs) -> bool {
				// Cannot be equal if the vector cannot possibly have as many elements
				// as the array. This allows the compiler to skip the element-wise
				// comparison in this case and simply return "false".
				N >= O && self[..] == other[..]
			}
		}
		)+
	};
}

gen_eq! {
	ArrayVec<T, N, ATOMIC1, A1>, ArrayVec<U, O, ATOMIC2, A2> [const O: usize, A1: Allocator, A2: Allocator, const ATOMIC1: bool, const ATOMIC2: bool];
	ArrayVec<T, N, ATOMIC, A>, &[U];
	ArrayVec<T, N, ATOMIC, A>, &mut [U];
	&[T], ArrayVec<U, N, ATOMIC, A>;
	&mut [T], ArrayVec<U, N, ATOMIC, A>;
	ArrayVec<T, N, ATOMIC, A>, [U];
	[T], ArrayVec<U, N, ATOMIC, A>;
	Unique<'_, T, N, A1, ATOMIC1>, Unique<'_, U, O, A2, ATOMIC2> [const O: usize, A1: Allocator, A2: Allocator, const ATOMIC1: bool, const ATOMIC2: bool];
	Unique<'_, T, N, A1, ATOMIC1>, ArrayVec<U, O, ATOMIC2, A2> [const O: usize, A1: Allocator, A2: Allocator, const ATOMIC1: bool, const ATOMIC2: bool];
	ArrayVec<T, N, ATOMIC1, A1>, Unique<'_, U, O, A2, ATOMIC2> [const O: usize, A1: Allocator, A2: Allocator, const ATOMIC1: bool, const ATOMIC2: bool];
	Unique<'_, T, N, A, ATOMIC>, &[U];
	Unique<'_, T, N, A, ATOMIC>, &mut [U];
	&[T], Unique<'_, U, N, A, ATOMIC>;
	&mut [T], Unique<'_, U, N, A, ATOMIC>;
	Unique<'_, T, N, A, ATOMIC>, [U];
	[T], Unique<'_, U, N, A, ATOMIC>;
}
	
gen_const_eq! {
	ArrayVec<T, N, ATOMIC, A>, [U; O];
	ArrayVec<T, N, ATOMIC, A>, &[U; O];
	ArrayVec<T, N, ATOMIC, A>, &mut [U; O];
	[T; O], ArrayVec<U, N, ATOMIC, A>;
	&[T; O], ArrayVec<U, N, ATOMIC, A>;
	&mut [T; O], ArrayVec<U, N, ATOMIC, A>;
	Unique<'_, T, N, A, ATOMIC>, [U; O];
	Unique<'_, T, N, A, ATOMIC>, &[U; O];
	Unique<'_, T, N, A, ATOMIC>, &mut [U; O];
	[T; O], Unique<'_, U, N, A, ATOMIC>;
	&[T; O], Unique<'_, U, N, A, ATOMIC>;
	&mut [T; O], Unique<'_, U, N, A, ATOMIC>;
}
