// Copyright 2025 - Strixpyrr
// SPDX-License-Identifier: Apache-2.0

use core::alloc::Allocator;
use super::{Deque, Unique};

macro_rules! gen_eq {
	() => { };
	($lhs:ty, $rhs:ty;$($next:tt)*) => {
		gen_eq! { $lhs, $rhs [A: Allocator, const ATOMIC: bool];$($next)* }
	};
    ($lhs:ty, $rhs:ty [$($params:tt)+];$($next:tt)*) => {
		impl<T: PartialEq<U>, U, $($params)+> PartialEq<$rhs> for $lhs {
			fn eq(&self, other: &$rhs) -> bool {
				todo!()
			}
		}
		gen_eq! { $($next)* }
	};
}

gen_eq! {
	Deque<T, ATOMIC1, A1>, Deque<U, ATOMIC2, A2> [A1: Allocator, A2: Allocator, const ATOMIC1: bool, const ATOMIC2: bool];
	Deque<T, ATOMIC, A>, &[U];
	Deque<T, ATOMIC, A>, &mut [U];
	&[T], Deque<U, ATOMIC, A>;
	&mut [T], Deque<U, ATOMIC, A>;
	Deque<T, ATOMIC, A>, [U];
	[T], Deque<U, ATOMIC, A>;
	Unique<'_, T, A1, ATOMIC1>, Unique<'_, U, A2, ATOMIC2> [A1: Allocator, A2: Allocator, const ATOMIC1: bool, const ATOMIC2: bool];
	Unique<'_, T, A1, ATOMIC1>, Deque<U, ATOMIC2, A2> [A1: Allocator, A2: Allocator, const ATOMIC1: bool, const ATOMIC2: bool];
	Deque<T, ATOMIC1, A1>, Unique<'_, U, A2, ATOMIC2> [A1: Allocator, A2: Allocator, const ATOMIC1: bool, const ATOMIC2: bool];
	Unique<'_, T, A, ATOMIC>, &[U];
	Unique<'_, T, A, ATOMIC>, &mut [U];
	&[T], Unique<'_, U, A, ATOMIC>;
	&mut [T], Unique<'_, U, A, ATOMIC>;
	Unique<'_, T, A, ATOMIC>, [U];
	[T], Unique<'_, U, A, ATOMIC>;
	Deque<T, ATOMIC, A>, [U; N]           [A: Allocator, const ATOMIC: bool, const N: usize];
	Deque<T, ATOMIC, A>, &[U; N]          [A: Allocator, const ATOMIC: bool, const N: usize];
	Deque<T, ATOMIC, A>, &mut [U; N]      [A: Allocator, const ATOMIC: bool, const N: usize];
	[T; N], Deque<U, ATOMIC, A>           [A: Allocator, const ATOMIC: bool, const N: usize];
	&[T; N], Deque<U, ATOMIC, A>          [A: Allocator, const ATOMIC: bool, const N: usize];
	&mut [T; N], Deque<U, ATOMIC, A>      [A: Allocator, const ATOMIC: bool, const N: usize];
	Unique<'_, T, A, ATOMIC>, [U; N]      [A: Allocator, const ATOMIC: bool, const N: usize];
	Unique<'_, T, A, ATOMIC>, &[U; N]     [A: Allocator, const ATOMIC: bool, const N: usize];
	Unique<'_, T, A, ATOMIC>, &mut [U; N] [A: Allocator, const ATOMIC: bool, const N: usize];
	[T; N], Unique<'_, U, A, ATOMIC>      [A: Allocator, const ATOMIC: bool, const N: usize];
	&[T; N], Unique<'_, U, A, ATOMIC>     [A: Allocator, const ATOMIC: bool, const N: usize];
	&mut [T; N], Unique<'_, U, A, ATOMIC> [A: Allocator, const ATOMIC: bool, const N: usize];
}
