// Copyright 2024 - Strixpyrr
// SPDX-License-Identifier: Apache-2.0

#![allow(unused)]

#![cfg_attr(not(feature = "std"), no_std)]
#![feature(allocator_api)]
#![cfg_attr(
	feature = "unstable-traits",
	feature(
		exact_size_is_empty,
		iter_advance_by,
		iter_next_chunk,
		trusted_len,
		try_trait_v2,
		extend_one,
		coerce_unsized,
		slice_index_methods,
	)
)]
#![feature(specialization)]
#![feature(slice_range)]
#![feature(ptr_metadata)]
#![feature(layout_for_ptr)]
#![deny(
	clippy::alloc_instead_of_core,
	clippy::as_pointer_underscore,
	clippy::as_underscore,
	clippy::assertions_on_result_states,
	clippy::cfg_not_test,
	clippy::clone_on_ref_ptr,
	clippy::decimal_literal_representation,
	clippy::deref_by_slicing,
	clippy::else_if_without_else,
	clippy::empty_drop,
	clippy::empty_enum_variants_with_brackets,
	clippy::empty_structs_with_brackets,
	clippy::error_impl_error,
	clippy::exhaustive_enums,
	clippy::field_scoped_visibility_modifiers,
	clippy::if_then_some_else_none,
	clippy::impl_trait_in_params,
	clippy::infinite_loop,
	clippy::map_err_ignore,
	clippy::mem_forget,
	clippy::missing_assert_message,
	clippy::missing_errors_doc,
	clippy::missing_panics_doc,
	clippy::missing_safety_doc,
	clippy::multiple_unsafe_ops_per_block,
	clippy::panic,
	clippy::partial_pub_fields,
	clippy::redundant_type_annotations,
	clippy::ref_patterns,
	clippy::renamed_function_params,
	clippy::semicolon_inside_block,
	clippy::std_instead_of_alloc,
	clippy::std_instead_of_core,
	clippy::undocumented_unsafe_blocks,
	clippy::unwrap_used,
)]

//! # `sharevec`
//! 
//! `sharevec` is a collection of reference-counted vector-like collections. They can be cloned
//! in *O*(1) time, sharing their underlying memory between clones rather than cloning each element.
//! Resizing (like [`Vec`]) and fixed capacity, single and double-ended, and [`Rc`]/[`Arc`]-based
//! versions are provided.
//! 
//! | Type | Layout | [`Clone`] complexity | Length |
//! |------|--------|----------------------|--------|
//! | [`Vec<T>`][`Vec`]                        | pointer, capacity, length | *O*(n) | Growable |
//! | [`Box<[T]>`][Box]                        | pointer, length           | *O*(n) | Fixed    |
//! | [`Rc`]/[`Arc<[T]>`][`Arc`]               | pointer, length           | *O*(1) | Fixed    |
//! | [`Rc`][RcVec]/[`ArcVec<T>`]              | pointer, capacity, length | *O*(1) | Growable |
//! | [`FixedCapacityVec<T, N>`] (external crate) | pointer, length        | *O*(n) | Growable within fixed capacity |
//! | [`Box<[T; N]>`][Box]                     | pointer                   | *O*(n) | Fixed    |
//! | [`Rc`]/[`Arc<[T; N]>`][`Arc`]            | pointer                   | *O*(1) | Fixed    |
//! | [`Rc`][RcArrayVec]/[`ArcArrayVec<T, N>`] | pointer, length           | *O*(1) | Growable within fixed capacity |
//! 
//! # Mutability Rules
//! 
//! Modifying memory though a shared reference is not generally allowed in Rust (except by explicit
//! opt-in to interior mutability); only one mutable reference can be held at any given time. The
//! standard library's reference counter types, [`Rc`] and [`Arc`], uphold this mutable non-aliasing
//! rule at runtime by checking that they hold the *unique* reference to the data they point to.
//! 
//! Similarly, any of the vector types in this crate may be modified, as long as they hold the only
//! (unique) *strong* reference to their underlying allocation, and the modification does not resize
//! their capacity. To resize in-place, the vector allocation must additionally have no *weak*
//! references. If a vector is shared, its contents are "clone-on-write". Shared contents must be
//! cloned into a new allocation before the vector can be modified.
//! 
//! So, if the vector has been cloned, an additional strong reference has been created, and both the
//! original and cloned vector become immutable. Once all other strong references drop, the vector
//! may be modified again. The vector reference may be downgraded into a weak reference to prevent
//! resizing in-place or deallocation of a vector's capacity, but allow mutability of its existing
//! capacity.
//! 
//! ## Nightly Requirement
//! 
//! This crate requires the nightly compiler, as it makes heavy use of the `allocation_api` feature
//! flag. Not much can be done to avoid this currently. Attributes cannot be applied to generic
//! arguments, rendering conditional compilation with `#[cfg]` very cumbersome. This requirement may
//! be lifted later.
//! 
//! [`Vec`]: alloc::vec::Vec
//! [`Rc`]: alloc::rc::Rc
//! [`Arc`]: alloc::sync::Arc
//! [Box]: alloc::boxed::Box
//! [RcVec]: vec::rc::Vec
//! [`ArcVec<T>`]: vec::arc::Vec
//! [`FixedCapacityVec<T, N>`]: https://crates.io/crates/fixed-capacity-vec
//! [RcArrayVec]: array::vec::rc::ArrayVec
//! [`ArcArrayVec<T, N>`]: array::vec::arc::ArrayVec

// Todo: resolve a problem with removal and truncation semantics on shared vectors. If all vectors
//  attempt to remove the same element, which vector should drop the element? How will the last
//  vector to remove the element know the element is no longer present in any of its siblings, and
//  properly drop the element? Is it acceptable for shared vectors to never call droppers, since
//  that's not a soundness guarantee Rust makes? It's infeasible to store all the length information
//  for each share in the allocation, or strong ref-counts for each element, and there doesn't appear
//  to be any other way for this to work. For now, any removal methods will be clone-on-write, but this
//  is neither desirable long-term nor reasonably expected behavior.

// Todo: should methods which panic have the `track_caller` attribute? All the standard implementations
//  have it, but it's odd to have a non-internal method be invisible in the backtrace.

// Todo: weak references break the uniqueness model. While a `Unique` wrapper holds a reference to
//  to a vector, any existing weak references may be upgraded, causing the vector to be shared while
//  uniqueness was supposed to be upheld. As a workaround, for the `Unique` wrapper to exist the vector
//  must be both weakly and strongly unique. The fallible modification methods don't appear to suffer
//  the same limitation.

// Todo: for clone-on-write Drain, instead of cloning the entire collection out of a share, set the
//  length then clone out of Iter. If the iterator is dropped halfway, only that many elements are
//  cloned.
//  IntoIter can work similarly, without setting the length. On every iteration, it would have to
//  check if it is unique. If it becomes unique halfway through, it would have to switch to moving
//  elements and drop the previously cloned elements when it itself is dropped.
// Todo: IterMut should clone its slice of shared allocation lazily (only if Iterator::next is
//  called). If the slice is empty, such as `deque.range_mut(..0)`, nothing is cloned.

// Todo: add examples on each type's top-level documentation.

extern crate alloc;

pub mod error;
mod macros;
pub mod marker;
#[cfg(feature = "vec")]
pub mod vec;
#[cfg(feature = "deque")]
pub mod deque;
#[cfg(any(feature = "array-deque", feature = "array-vec"))]
pub mod array;
mod raw;
mod internal;

pub mod prelude {
	pub use crate::error::Shared;
	#[cfg(any(feature = "array-deque", feature = "array-vec"))]
	pub use crate::array::{FullCapacity, TryExtend, TryFromSlice, TryInsert};
	#[cfg(feature = "array-deque")]
	pub use crate::array::deque::rc::{
		ArrayDeque as RcArrayDeque,
	};
	#[cfg(all(target_has_atomic = "ptr", feature = "array-deque"))]
	pub use crate::array::deque::arc::{
		ArrayDeque as ArcArrayDeque,
		Unique as UniqueArcArrayDeque,
	};
	#[cfg(feature = "array-vec")]
	pub use crate::array::vec::rc::{
		ArrayVec as RcArrayVec,
		Unique as UniqueRcArrayVec,
	};
	#[cfg(all(target_has_atomic = "ptr", feature = "array-vec"))]
	pub use crate::array::vec::arc::{
		ArrayVec as ArcArrayVec,
		Unique as UniqueArcArrayVec,
	};
	#[cfg(feature = "deque")]
	pub use crate::deque::rc::{
		Deque as RcDeque,
		Unique as UniqueRcDeque
	};
	#[cfg(all(target_has_atomic = "ptr", feature = "deque"))]
	pub use crate::deque::arc::{
		Deque as ArcDeque,
		Unique as UniqueArcDeque,
	};
	#[cfg(feature = "vec")]
	pub use crate::vec::rc::{
		Vec as RcVec,
		Unique as UniqueRcVec,
	};
	#[cfg(all(target_has_atomic = "ptr", feature = "vec"))]
	pub use crate::vec::arc::{
		Vec as ArcVec,
		Unique as UniqueArcVec,
	};
}
