// Copyright 2025 - Strixpyrr
// SPDX-License-Identifier: Apache-2.0

use core::alloc::Allocator;
use crate::array::deque::ArrayDeque;
use crate::array::deque::unique::Unique as ArrayDequeUnique;
use crate::array::vec::unique::Unique as ArrayVecUnique;
use crate::array::vec::ArrayVec;
use crate::deque::Deque;
use crate::deque::unique::Unique as DequeUnique;
use crate::vec::Vec;
use crate::vec::unique::Unique as VecUnique;

/// A marker for any reference-counted vector type in this crate.
pub trait RcVector<T, A: Allocator, const ATOMIC: bool>: private::Vec<ATOMIC> { }
/// A marker for any unique wrapper type in this crate.
pub trait UniqueVector<T, A: Allocator, const ATOMIC: bool>: RcVector<T, A, ATOMIC> { }

impl<T, const N: usize, A: Allocator, const ATOMIC: bool> RcVector<T, A, ATOMIC> for ArrayVec<T, N, ATOMIC, A> { }
impl<T, const N: usize, A: Allocator, const ATOMIC: bool> RcVector<T, A, ATOMIC> for ArrayVecUnique<'_, T, N, A, ATOMIC> { }
impl<T, const N: usize, A: Allocator, const ATOMIC: bool> RcVector<T, A, ATOMIC> for ArrayDeque<T, N, ATOMIC, A> { }
impl<T, const N: usize, A: Allocator, const ATOMIC: bool> RcVector<T, A, ATOMIC> for ArrayDequeUnique<'_, T, N, A, ATOMIC> { }
impl<T, A: Allocator, const ATOMIC: bool> RcVector<T, A, ATOMIC> for Vec<T, ATOMIC, A> { }
impl<T, A: Allocator, const ATOMIC: bool> RcVector<T, A, ATOMIC> for VecUnique<'_, T, A, ATOMIC> { }
impl<T, A: Allocator, const ATOMIC: bool> RcVector<T, A, ATOMIC> for Deque<T, ATOMIC, A> { }
impl<T, A: Allocator, const ATOMIC: bool> RcVector<T, A, ATOMIC> for DequeUnique<'_, T, A, ATOMIC> { }

impl<T, const N: usize, A: Allocator, const ATOMIC: bool> UniqueVector<T, A, ATOMIC> for ArrayVecUnique<'_, T, N, A, ATOMIC> { }
impl<T, const N: usize, A: Allocator, const ATOMIC: bool> UniqueVector<T, A, ATOMIC> for ArrayDequeUnique<'_, T, N, A, ATOMIC> { }
impl<T, A: Allocator, const ATOMIC: bool> UniqueVector<T, A, ATOMIC> for VecUnique<'_, T, A, ATOMIC> { }
impl<T, A: Allocator, const ATOMIC: bool> UniqueVector<T, A, ATOMIC> for DequeUnique<'_, T, A, ATOMIC> { }

pub(crate) mod private {
	use core::alloc::Allocator;

	pub trait Vec<const ATOMIC: bool> { }

	impl<T, const N: usize, A: Allocator, const ATOMIC: bool> Vec<ATOMIC> for super::ArrayVec<T, N, ATOMIC, A> { }
	impl<T, const N: usize, A: Allocator, const ATOMIC: bool> Vec<ATOMIC> for super::ArrayVecUnique<'_, T, N, A, ATOMIC> { }
	impl<T, const N: usize, A: Allocator, const ATOMIC: bool> Vec<ATOMIC> for super::ArrayDeque<T, N, ATOMIC, A> { }
	impl<T, const N: usize, A: Allocator, const ATOMIC: bool> Vec<ATOMIC> for super::ArrayDequeUnique<'_, T, N, A, ATOMIC> { }
	impl<T, A: Allocator, const ATOMIC: bool> Vec<ATOMIC> for super::Vec<T, ATOMIC, A> { }
	impl<T, A: Allocator, const ATOMIC: bool> Vec<ATOMIC> for super::VecUnique<'_, T, A, ATOMIC> { }
	impl<T, A: Allocator, const ATOMIC: bool> Vec<ATOMIC> for super::Deque<T, ATOMIC, A> { }
	impl<T, A: Allocator, const ATOMIC: bool> Vec<ATOMIC> for super::DequeUnique<'_, T, A, ATOMIC> { }
}
