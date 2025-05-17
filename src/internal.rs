// Copyright 2025 - Strixpyrr
// SPDX-License-Identifier: Apache-2.0

pub trait TypeSize: Sized {
	const IS_ZST: bool = size_of::<Self>() == 0;
}

impl<T> TypeSize for T { }

/// A version of the [`Clone`] trait accessible when a generic parameter can't have an explicit
/// [`Clone`] bound.
pub trait UnsafeClone: Sized {
	/// # Safety
	/// 
	/// This must only be called if the type is known at runtime to implement [`Clone`].
	unsafe fn clone_unsafe(&self) -> Self;
	
	unsafe fn clone_from_slice_unsafe(dst: &mut [Self], src: &[Self]);
}

impl<T: Clone> UnsafeClone for T {
	unsafe fn clone_unsafe(&self) -> Self {
		self.clone()
	}

	unsafe fn clone_from_slice_unsafe(dst: &mut [Self], src: &[Self]) {
		dst.clone_from_slice(src);
	}
}

impl<T> UnsafeClone for T {
	default unsafe fn clone_unsafe(&self) -> Self {
		unreachable!()
	}

	default unsafe fn clone_from_slice_unsafe(_dst: &mut [Self], _src: &[Self]) {
		unreachable!()
	}
}
