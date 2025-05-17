// Copyright 2025 - Strixpyrr
// SPDX-License-Identifier: Apache-2.0

use alloc::alloc::handle_alloc_error;
use alloc::vec;
use core::alloc::{Allocator, Layout, LayoutError};
use core::cell::Cell;
use core::fmt::Pointer;
use core::marker::PhantomData;
use core::{mem, ptr, slice};
use core::mem::{ManuallyDrop, MaybeUninit};
use core::ops::Range;
use core::ptr::{NonNull, Pointee};
#[cfg(target_has_atomic = "ptr")]
use core::sync::atomic::{AtomicUsize, Ordering};
use inner::RawInnerVec;
use crate::error::Shared;
use crate::marker::private::Vec as VecTrait;

pub mod inner;

#[repr(C)]
pub struct VecInner<S: ?Sized = ()> {
	strong: Cell<usize>,
	weak: Cell<usize>,
	len: usize,
	store: S,
}

#[repr(C)]
pub struct DequeInner<S: ?Sized = ()> {
	strong: Cell<usize>,
	weak: Cell<usize>,
	head: usize,
	len: usize,
	store: S,
}

/// An inner type without its store field (i.e. `VecInner<()>`).
pub trait InnerBase: Sized {
	const BASE_LAYOUT: Layout = Layout::new::<Self>();
	const BASE_SIZE: usize = size_of::<Self>();
	
	type WithStore<S: ?Sized>: ?Sized;
	
	/// Returns an inner pointer from an offset pointer to the store.
	fn from_store(ptr: NonNull<()>) -> NonNull<Self> {
		let byte_ptr = ptr.cast::<u8>();
		// Safety: offset itself is safe. The caller promises to uphold the pointer's validity on
		//  usage.
		let offset_ptr = unsafe { byte_ptr.sub(Self::BASE_SIZE) };
		offset_ptr.cast()
	}
	
	/// Returns an offset pointer to the strong count.
	fn strong(ptr: NonNull<Self>) -> NonNull<Cell<usize>>;
	/// Returns an offset pointer to the weak count.
	fn weak  (ptr: NonNull<Self>) -> NonNull<Cell<usize>>;
	/// Returns an offset pointer to the length.
	fn len   (ptr: NonNull<Self>) -> NonNull<usize>;
	/// Returns an offset pointer to the store.
	fn store (ptr: NonNull<Self>) -> NonNull<()>;

	/// Initializes the strong and weak counts, and the length and head (for deques).
	///
	/// # Safety
	///
	/// The pointer must uniquely reference the inner value, and be valid for dereferencing.
	unsafe fn init_counts(ptr: NonNull<Self>);

	/// Reads the strong count.
	///
	/// # Safety
	///
	/// The pointer must be valid for dereferencing.
	unsafe fn strong_count<const ATOMIC: bool>(ptr: NonNull<Self>) -> usize {
		get_count::<ATOMIC>(Self::strong(ptr))
	}
	/// Increments the strong count, returning the new count.
	///
	/// # Safety
	///
	/// The pointer must be valid for dereferencing.
	unsafe fn strong_inc<const ATOMIC: bool>(ptr: NonNull<Self>) -> usize {
		inc_count::<ATOMIC>(Self::strong(ptr))
	}
	/// Decrements the strong count, returning the new count.
	///
	/// # Safety
	///
	/// The pointer must be valid for dereferencing.
	unsafe fn strong_dec<const ATOMIC: bool>(ptr: NonNull<Self>) -> usize {
		dec_count::<ATOMIC>(Self::strong(ptr))
	}

	/// Reads the weak count.
	///
	/// # Safety
	///
	/// The pointer must be valid for dereferencing.
	unsafe fn weak_count<const ATOMIC: bool>(ptr: NonNull<Self>) -> usize {
		get_count::<ATOMIC>(Self::weak(ptr))
	}
	/// Increments the weak count, returning the new count.
	///
	/// # Safety
	///
	/// The pointer must be valid for dereferencing.
	unsafe fn weak_inc<const ATOMIC: bool>(ptr: NonNull<Self>) -> usize {
		inc_count::<ATOMIC>(Self::weak(ptr))
	}
	/// Decrements the weak count, returning the new count.
	///
	/// # Safety
	///
	/// The pointer must be valid for dereferencing.
	unsafe fn weak_dec<const ATOMIC: bool>(ptr: NonNull<Self>) -> usize {
		dec_count::<ATOMIC>(Self::weak(ptr))
	}
}

fn get_count<const ATOMIC: bool>(ptr: NonNull<Cell<usize>>) -> usize {
	mut_count::<ATOMIC>(
		ptr,
		Cell::get,
		#[cfg(target_has_atomic = "ptr")]
		|v| v.load(Ordering::Acquire)
	)
}

fn inc_count<const ATOMIC: bool>(ptr: NonNull<Cell<usize>>) -> usize {
	mut_count::<ATOMIC>(
		ptr,
		|v| {
			let x = v.get() + 1;
			v.set(x);
			x
		},
		#[cfg(target_has_atomic = "ptr")]
		|v| v.fetch_add(1, Ordering::AcqRel) + 1
	)
}

fn dec_count<const ATOMIC: bool>(ptr: NonNull<Cell<usize>>) -> usize {
	mut_count::<ATOMIC>(
		ptr,
		|v| {
			let x = v.get() - 1;
			v.set(x);
			x
		},
		#[cfg(target_has_atomic = "ptr")]
		|v| v.fetch_sub(1, Ordering::AcqRel) - 1
	)
}

fn mut_count<const ATOMIC: bool>(
	ptr: NonNull<Cell<usize>>,
	default_fn: fn(&Cell<usize>) -> usize,
	#[cfg(target_has_atomic = "ptr")]
	atomic_fn: fn(&AtomicUsize) -> usize,
) -> usize {
	match ATOMIC {
		#[cfg(target_has_atomic = "ptr")]
		true =>
			// Safety: `ptr` was created from a `NonNull` pointer. `AtomicUsize` has the same layout
			//  as `Cell<usize>`.
			unsafe {
				atomic_fn(ptr.cast::<AtomicUsize>().as_ref())
			},
		_ =>
			// Safety: `ptr` was created from a `NonNull` pointer.
			unsafe {
				default_fn(ptr.as_ref())
			}
	}
}

macro_rules! project {
    ($ptr:ident->$field:ident) => {
		NonNull::new_unchecked(&raw mut (*$ptr.as_ptr()).$field)
	};
}

impl InnerBase for VecInner {
	type WithStore<S: ?Sized> = VecInner<S>;
	
	fn strong(ptr: NonNull<Self>) -> NonNull<Cell<usize>> {
		// Safety: this projection is valid if the given pointer is valid.
		unsafe {
			project!(ptr->strong)
		}
	}

	fn weak(ptr: NonNull<Self>) -> NonNull<Cell<usize>> {
		// Safety: this projection is valid if the given pointer is valid.
		unsafe {
			project!(ptr->weak)
		}
	}

	fn len(ptr: NonNull<Self>) -> NonNull<usize> {
		// Safety: this projection is valid if the given pointer is valid.
		unsafe {
			project!(ptr->len)
		}
	}

	fn store(ptr: NonNull<Self>) -> NonNull<()> {
		// Safety: this projection is valid if the given pointer is valid.
		unsafe {
			project!(ptr->store)
		}
	}

	unsafe fn init_counts(mut ptr: NonNull<Self>) {
		let Self { strong, weak, len, .. } = ptr.as_mut();
		*strong = Cell::new(1);
		*weak   = Cell::new(0);
		*len    = 0;
	}
}

impl InnerBase for DequeInner {
	type WithStore<S: ?Sized> = DequeInner<S>;
	
	fn strong(ptr: NonNull<Self>) -> NonNull<Cell<usize>> {
		// Safety: this projection is valid if the given pointer is valid.
		unsafe {
			project!(ptr->strong)
		}
	}

	fn weak(ptr: NonNull<Self>) -> NonNull<Cell<usize>> {
		// Safety: this projection is valid if the given pointer is valid.
		unsafe {
			project!(ptr->weak)
		}
	}

	fn len(ptr: NonNull<Self>) -> NonNull<usize> {
		// Safety: this projection is valid if the given pointer is valid.
		unsafe {
			project!(ptr->len)
		}
	}

	fn store(ptr: NonNull<Self>) -> NonNull<()> {
		// Safety: this projection is valid if the given pointer is valid.
		unsafe {
			project!(ptr->store)
		}
	}

	unsafe fn init_counts(mut ptr: NonNull<Self>) {
		let Self { strong, weak, head, len, .. } = ptr.as_mut();
		*strong = Cell::new(1);
		*weak   = Cell::new(0);
		*head   = 0;
		*len    = 0;
	}
}

impl DequeInner {
	fn head(ptr: NonNull<Self>) -> NonNull<usize> {
		// Safety: this projection is valid if the given pointer is valid.
		unsafe {
			project!(ptr->head)
		}
	}
}

pub trait Store: AsRef<[Self::T]> {
	type T;
	type Capacity: Copy + Default;
	
	fn capacity(cap: Self::Capacity) -> usize;
}

impl<T, const N: usize> Store for [T; N] {
	type T = T;
	type Capacity = ();

	fn capacity(_: ()) -> usize { N }
}

impl<T> Store for [T] {
	type T = T;
	type Capacity = usize;

	fn capacity(cap: usize) -> usize { cap }
}

pub type RawDeque<S: ?Sized, A> = RawCollection<S, DequeInner, A>;
pub type RawVec  <S: ?Sized, A> = RawCollection<S,   VecInner, A>;

pub struct RawCollection<S: ?Sized + Store, I, A> {
	inner: RawInnerVec<A>,
	cap: S::Capacity,
	_i: PhantomData<I>,
}

impl<T, I, A: Allocator> RawCollection<[T], I, A> {
	pub const fn dangling(alloc: A) -> Self {
		Self {
			inner: RawInnerVec::dangling(alloc),
			cap: 0,
			_i: PhantomData,
		}
	}
}

impl<T, const N: usize, I, A: Allocator> RawCollection<[T; N], I, A> {
	pub const fn dangling(alloc: A) -> Self {
		Self {
			inner: RawInnerVec::dangling(alloc),
			cap: (),
			_i: PhantomData,
		}
	}
}

impl<T, I: InnerBase, A: Allocator> RawCollection<[T], I, A> {
	#[track_caller]
	pub fn with_capacity(cap: usize, alloc: A) -> Self {
		Self {
			inner: RawInnerVec::with_capacity(
				cap,
				alloc,
				I::BASE_LAYOUT,
				Layout::new::<T>(),
			),
			cap,
			_i: PhantomData
		}.init()
	}

	pub fn try_with_capacity(cap: usize, alloc: A) -> Result<Self, AllocError> {
		RawInnerVec::try_with_capacity(
			cap,
			alloc,
			I::BASE_LAYOUT,
			Layout::new::<T>(),
		).map(|inner|
			Self { inner, cap, _i: PhantomData }.init()
		)
	}

	pub unsafe fn from_raw_parts(ptr: *mut T, cap: usize, alloc: A) -> Self {
		Self {
			inner: RawInnerVec::from_raw_parts(ptr.cast(), alloc),
			cap,
			_i: PhantomData
		}
	}

	pub unsafe fn from_non_null(ptr: NonNull<T>, cap: usize, alloc: A) -> Self {
		Self {
			inner: RawInnerVec::from_non_null(ptr.cast(), alloc),
			cap,
			_i: PhantomData
		}
	}
}

impl<T, const N: usize, I: InnerBase, A: Allocator> RawCollection<[T; N], I, A>
where
	I::WithStore<[T; N]>: Sized,
{
	#[track_caller]
	pub fn new(alloc: A) -> Self {
		match Self::try_new(alloc) {
			Ok(v) => v.init(),
			Err(e) => e.handle()
		}
	}

	pub fn try_new(alloc: A) -> Result<Self, AllocError> {
		Ok(match N {
			0 => Self::dangling(alloc),
			_ => Self {
				inner: RawInnerVec::allocate(
					Layout::new::<I::WithStore<[T; N]>>(),
					alloc
				)?,
				cap: (),
				_i: PhantomData
			}.init()
		})
	}

	pub unsafe fn from_raw_parts(ptr: *mut T, alloc: A) -> Self {
		Self {
			inner: RawInnerVec::from_raw_parts(ptr.cast(), alloc),
			cap: (),
			_i: PhantomData
		}
	}

	pub unsafe fn from_non_null(ptr: NonNull<T>, alloc: A) -> Self {
		Self {
			inner: RawInnerVec::from_non_null(ptr.cast(), alloc),
			cap: (),
			_i: PhantomData
		}
	}
}

impl<S: ?Sized + Store, I: InnerBase, A: Allocator> RawCollection<S, I, A> {
	fn init(self) -> Self {
		let inner = self.inner.inner_ptr::<I>();
		// Safety: `init` is only called when the vector is created.
		unsafe {
			I::init_counts(inner);
		}
		self
	}
}

pub fn check_size(size: usize) -> Result<(), AllocError> {
	if usize::BITS < 64 && size > isize::MAX as usize {
		Err(AllocError::CapacityOverflow)
	} else {
		Ok(())
	}
}

pub enum AllocError {
	CapacityOverflow,
	Alloc {
		layout: Layout
	}
}

impl AllocError {
	#[allow(clippy::panic)]
	#[cold]
	#[inline(never)]
	#[track_caller]
	pub fn handle(self) -> ! {
		match self {
			Self::CapacityOverflow => panic!("capacity overflow"),
			Self::Alloc { layout } => handle_alloc_error(layout)
		}
	}
}

impl From<LayoutError> for AllocError {
	fn from(_: LayoutError) -> Self {
		Self::CapacityOverflow
	}
}

impl From<AllocError> for core::alloc::AllocError {
	fn from(_: AllocError) -> Self {
		Self
	}
}

impl<T, const N: usize, I: InnerBase, A: Allocator> RawCollection<[T; N], I, A> {
	pub fn into_slice(self) -> RawCollection<[T], I, A> {
		RawCollection {
			inner: self.inner,
			cap: N,
			_i: PhantomData,
		}
	}
}

impl<S: ?Sized + Store, I: InnerBase, A: Allocator> RawCollection<S, I, A> {
	pub fn inner_ptr(&self) -> NonNull<I> {
		self.inner.inner_ptr()
	}
	
	pub fn ptr(&self) -> NonNull<S::T> {
		self.inner.ptr(I::BASE_LAYOUT)
	}
	
	pub fn allocator(&self) -> &A {
		self.inner.allocator()
	}
	
	pub fn inner_len(&self) -> usize {
		if self.inner.is_dangling() {
			0
		} else {
			// Safety: the pointer is checked to be not dangling.
			unsafe {
				I::len(self.inner_ptr()).read()
			}
		}
	}
	
	pub fn capacity(&self) -> usize {
		S::capacity(self.cap)
	}
	
	pub fn strong_count<const ATOMIC: bool>(&self) -> Option<usize> {
		// Safety: the pointer is not dangling.
		(!self.inner.is_dangling()).then(|| unsafe {
			I::strong_count::<ATOMIC>(self.inner_ptr())
		})
	}
	
	pub fn strong_inc<const ATOMIC: bool>(&self) -> Option<usize> {
		// Safety: the pointer is not dangling.
		(!self.inner.is_dangling()).then(|| unsafe {
			I::strong_inc::<ATOMIC>(self.inner_ptr())
		})
	}
	
	pub fn strong_dec<const ATOMIC: bool>(&self) -> Option<usize> {
		// Safety: the pointer is not dangling.
		(!self.inner.is_dangling()).then(|| unsafe {
			I::strong_dec::<ATOMIC>(self.inner_ptr())
		})
	}
	
	pub fn weak_count<const ATOMIC: bool>(&self) -> Option<usize> {
		// Safety: the pointer is not dangling.
		(!self.inner.is_dangling()).then(|| unsafe {
			I::weak_count::<ATOMIC>(self.inner_ptr())
		})
	}
	
	pub fn weak_inc<const ATOMIC: bool>(&self) -> Option<usize> {
		// Safety: the pointer is not dangling.
		(!self.inner.is_dangling()).then(|| unsafe {
			I::weak_inc::<ATOMIC>(self.inner_ptr())
		})
	}
	
	pub fn weak_dec<const ATOMIC: bool>(&self) -> Option<usize> {
		// Safety: the pointer is not dangling.
		(!self.inner.is_dangling()).then(|| unsafe {
			I::weak_dec::<ATOMIC>(self.inner_ptr())
		})
	}

	#[track_caller]
	pub fn share<const ATOMIC: bool>(&self) -> Self
	where
		A: Clone,
	{
		// Clone the inner vector first, in case cloning the allocator panics. If it does, the
		// strong count will not be incremented.
		let inner = self.inner.clone();

		self.strong_inc::<ATOMIC>();
		Self { inner, ..*self }
	}

	/// Deallocates the reference, possibly deallocating the underlying memory. The vector is
	/// reverted to a dangling state.
	pub fn drop_ref<const ATOMIC: bool>(&mut self, len: &mut usize) {
		let Some(strong) = self.strong_dec::<ATOMIC>() else {
			// The reference is already dangling.
			return
		};

		let len = mem::take(len);
		let capacity = S::capacity(mem::take(&mut self.cap));

		let Some(weak) = self.weak_count::<ATOMIC>() else {
			// The reference is guaranteed not to dangle by the decrement operation above.
			unreachable!()
		};

		let ptr = self.inner.inner_ptr::<I>();

		if strong != 0 {
			// No dropping or deallocation needed.
			return
		}

		// Safety: the reference is checked to be unique.
		unsafe {
			Self::deallocate(weak != 0, &mut self.inner, capacity);
		}
	}

	/// Drops the elements and deallocates memory if no weak references point to it.
	///
	/// # Safety
	///
	/// The vector must be unique.
	pub unsafe fn deallocate(
		is_weakly_shared: bool,
		inner: &mut RawInnerVec<A>,
		cap: usize,
	) {
		struct DropGuard<'a, A: Allocator> {
			inner: &'a mut RawInnerVec<A>,
			cap: usize,
			base_layout: Layout,
			elem_layout: Layout,
			is_weakly_shared: bool,
		}

		impl<A: Allocator> Drop for DropGuard<'_, A> {
			fn drop(&mut self) {
				if self.is_weakly_shared {
					return
				}

				// Safety: `ptr` is currently allocated in `alloc` with `layout`.
				unsafe {
					self.inner.deallocate(self.cap, self.base_layout, self.elem_layout);
				}
			}
		}

		// Deallocate even if `ptr::drop_in_place` panics.
		let g = DropGuard {
			inner,
			cap,
			base_layout: I::BASE_LAYOUT,
			elem_layout: Layout::new::<S::T>(),
			is_weakly_shared
		};
		
		let ptr = g.inner.inner_ptr::<I>();
		
		// Safety: the inner pointer is valid.
		let len = unsafe { I::len(ptr).read() };

		// Safety: `len` elements are initialized, the pointer is non-null and properly aligned.
		unsafe {
			let elem_ptr = I::store(ptr).cast::<S::T>().as_ptr();
			let slice_ptr = ptr::slice_from_raw_parts_mut(elem_ptr, len);
			ptr::drop_in_place(slice_ptr);
		}

		drop(g);
	}
	
	/// Sets the inner pointer.
	/// 
	/// # Safety
	/// 
	/// The current point must dangle.
	pub unsafe fn set_ptr(&mut self, ptr: NonNull<u8>) {
		self.inner.set_ptr(ptr);
	}

	/// Sets the lengths.
	///
	/// # Safety
	///
	/// The reference must not dangle. Elements within `new_len` must be initialized. The reference
	/// must be unique.
	pub unsafe fn set_len(&mut self, cur_len: &mut usize, new_len: usize) {
		*cur_len = new_len;
		self.set_inner_len(new_len);
	}
	/// Sets the inner length.
	///
	/// # Safety
	///
	/// The reference must not dangle. Elements within `new_len` must be initialized. The reference
	/// must be unique.
	pub unsafe fn set_inner_len(&mut self, len: usize) {
		let len_ptr = I::len(self.inner_ptr());
		len_ptr.write(len);
	}
}

impl<T, I: InnerBase, A: Allocator> RawCollection<[T], I, A> {
	#[track_caller]
	pub unsafe fn reserve(&mut self, len: usize, additional: usize) {
		self.inner.reserve(len, &mut self.cap, additional, I::BASE_LAYOUT, Layout::new::<T>());
	}
	
	pub unsafe fn try_reserve(&mut self, len: usize, additional: usize) -> Result<(), AllocError> {
		self.inner.try_reserve(len, &mut self.cap, additional, I::BASE_LAYOUT, Layout::new::<T>())
	}
	
	#[track_caller]
	pub unsafe fn reserve_exact(&mut self, len: usize, additional: usize) {
		self.inner.reserve_exact(len, &mut self.cap, additional, I::BASE_LAYOUT, Layout::new::<T>());
	}
	
	pub unsafe fn try_reserve_exact(&mut self, len: usize, additional: usize) -> Result<(), AllocError> {
		self.inner.try_reserve_exact(len, &mut self.cap, additional, I::BASE_LAYOUT, Layout::new::<T>())
	}
	
	#[track_caller]
	pub unsafe fn shrink(&mut self, cap: usize) {
		self.inner.shrink(&mut self.cap, cap, I::BASE_LAYOUT, Layout::new::<T>());
	}
}

impl<S: ?Sized + Store, A: Allocator> RawVec<S, A> {
	pub unsafe fn as_slice(&self, len: usize) -> &[S::T] {
		debug_assert!(self.inner_len() >= len, "the outer length should be within the inner length");
		slice::from_raw_parts(self.ptr().as_ptr(), len)
	}
	
	pub unsafe fn as_mut_slice(&mut self, len: usize) -> &mut [S::T] {
		debug_assert!(self.inner_len() >= len, "the outer length should be within the inner length");
		slice::from_raw_parts_mut(self.ptr().as_ptr(), len)
	}
	
	pub unsafe fn as_uninit_slice(&mut self, start: usize) -> &mut [MaybeUninit<S::T>] {
		slice::from_raw_parts_mut(
			self.ptr().add(start).as_ptr().cast(),
			self.capacity() - start
		)
	}
	
	/// Copies the contents into a new allocation, deallocating the old one. Used by `vec.as_unique`
	/// functions to disassociate weak pointers.
	///
	/// # Safety
	///
	/// The elements within `len` must be initialized. The reference must be unique.
	#[track_caller]
	pub unsafe fn copy_out(&mut self, len: usize) -> Result<(), AllocError> {
		// A non-atomic write is safe here, as we are operating on a unique
		// reference.
		self.strong_dec::<false>();

		// The outer length may have fallen out of sync with the inner length,
		// which would cause elements to be lost without dropping after copying.
		// To prevent this, these elements first need to be dropped.
		self.truncate(len);
		// Set the length to 0, as these elements will be moved out of this
		// pointer.
		self.set_inner_len(0);

		let capacity = self.capacity();
		let Some(ptr) = self.inner.copy_out(
			len,
			capacity,
			VecInner::<()>::BASE_LAYOUT,
			Layout::new::<S::T>(),
		)? else {
			return Ok(())
		};
		Ok(())
	}
	
	/// Sets the inner length, dropping elements after the length. This has the effect of bringing
	/// the outer length (which may differ between shared references) and the inner length in sync.
	/// 
	/// # Safety
	/// 
	/// `len` must be less than or equal to the number of currently initialized elements. The
	/// reference must be unique. The outer length should be set before calling.
	#[track_caller]
	pub unsafe fn truncate(&mut self, new_len: usize) {
		if self.inner.is_dangling() {
			return
		}
		
		let inner_len = self.inner_len();
		
		debug_assert!(
			inner_len >= new_len,
			"the inner length should be greater than or equal to the new length"
		);
		
		let remaining_len = inner_len - new_len;
		let slice = ptr::slice_from_raw_parts_mut(
			self.ptr().add(new_len).as_ptr(),
			remaining_len
		);
		
		// Push the new length to the inner pointer before dropping, in case
		// `T::drop` panics.
		self.set_inner_len(new_len);
		
		ptr::drop_in_place(slice);
	}

	/// Replaces the element at `index` with the last element, returning it.
	///
	/// # Safety
	///
	/// `index` must be less than the length of the vector. The reference must be unique.
	#[track_caller]
	pub unsafe fn swap_remove(&mut self, index: usize, len: &mut usize) -> S::T {
		// Minimally-generic code, outlined to reduce bloat
		unsafe fn do_swap<T>(base_ptr: *mut T, index: usize, last: usize) -> T {
			// We replace self[index] with the last element. Note that if the bounds invariant holds
			// there must be a last element (which can be self[index] itself).
			let value = base_ptr.add(index).read();
			ptr::copy(base_ptr.add(last), base_ptr.add(index), 1);
			value
		}

		// The outer length may have fallen out of sync with the inner length,
		// which would cause elements to be lost without dropping after swapping.
		// To prevent this, these elements first need to be dropped.
		self.truncate(*len);

		let last = *len - 1;

		let value = do_swap(self.ptr().as_ptr(), index, last);
		self.set_len(len, last);
		value
	}

	/// Removes and returns the element at `index`.
	///
	/// # Safety
	///
	/// `index` must be less than the length of the vector. The reference must be unique.
	#[track_caller]
	pub unsafe fn remove(&mut self, index: usize, len: &mut usize) -> S::T {
		// Minimally-generic code, outlined to reduce bloat
		unsafe fn do_move<T>(base_ptr: *mut T, index: usize, len: usize) -> T {
			let ptr = base_ptr.add(index);
			// Keep an unsafe copy of the value on the stack and in the vector
			// simultaneously.
			let value = ptr.read();
			// Shift everything back to fill the hole.
			ptr::copy(ptr.add(1), ptr, len - index - 1);
			// The copy is now the only remaining one, so it is safe to use.
			value
		}

		// The outer length may have fallen out of sync with the inner length,
		// which would cause elements to be lost without dropping after shifting
		// back. To prevent this, these elements first need to be dropped.
		self.truncate(*len);

		let value = do_move(self.ptr().as_ptr(), index, *len);
		self.set_len(len, *len - 1);
		value
	}

	/// Inserts `value` at `index`.
	///
	/// # Safety
	///
	/// `index` must be less than the length of the vector. The reference must be unique.
	#[track_caller]
	pub unsafe fn insert(&mut self, index: usize, len: &mut usize, value: S::T) {
		// Minimally-generic code, outlined to reduce bloat
		unsafe fn do_move<T>(base_ptr: *mut T, index: usize, value: T, len: usize) {
			let ptr = base_ptr.add(index);

			if index < len {
				// Shift everything forward, duplicating the element at `index` in
				// two consecutive places.
				ptr::copy(ptr, ptr.add(1), len - index);
			}

			// Overwrite the first copy at `index` with the value.
			ptr.write(value);
		}

		// The outer length may have fallen out of sync with the inner length,
		// which would cause elements to be lost without dropping after shifting
		// forward. To prevent this, these elements first need to be dropped.
		self.truncate(*len);

		do_move(self.ptr().as_ptr(), index, value, *len);
		self.set_len(len, *len + 1);
	}

	/// Removes elements for which `keep` returns `false`.
	///
	/// # Safety
	///
	/// The vector must be unique or empty.
	#[allow(clippy::impl_trait_in_params, reason = "private API")]
	#[allow(clippy::multiple_unsafe_ops_per_block)]
	#[track_caller]
	pub unsafe fn retain_mutable(&mut self, len: &mut usize, mut keep: impl FnMut(&mut S::T) -> bool) {
		let original_len = *len;
		
		if original_len == 0 {
			return
		}

		// The outer length may have fallen out of sync with the inner length,
		// which would cause elements to be lost without dropping after modifying.
		// To prevent this, these elements first need to be dropped.
		// This is placed *after* the length check to avoid inner truncation on
		// a shared empty vector.
		self.truncate(*len);

		// Avoid double drop if the drop guard is not executed, since we may
		// make some holes during the process.
		self.set_len(len, 0);

		// Vec: [Kept, Kept, Hole, Hole, Hole, Hole, Unchecked, Unchecked]
		//      |<-              processed len   ->| ^- next to check
		//                  |<-  deleted cnt     ->|
		//      |<-              original_len                          ->|
		// Kept: Elements which predicate returns true on.
		// Hole: Moved or dropped element slot.
		// Unchecked: Unchecked valid elements.
		//
		// This drop guard will be invoked if `keep` or `drop` of element panics. This shifts
		// unchecked elements to cover holes and `set_len` to the correct length. In cases when
		// predicate and `drop` never panic, it will be optimized out.
		struct DropGuard<'a, T> {
			inner_ptr: NonNull<VecInner<()>>,
			outer_len: &'a mut usize,
			processed_len: usize,
			deleted_count: usize,
			original_len: usize,
			_t: PhantomData<&'a mut T>,
		}
		
		impl<T> Drop for DropGuard<'_, T> {
			fn drop(&mut self) {
				if self.deleted_count > 0 {
					let ptr = VecInner::store(self.inner_ptr).cast::<T>().as_ptr();
					// Safety: the vector holds a unique reference. Trailing unchecked items are
					//  valid as they remain untouched.
					unsafe {
						ptr::copy(
							ptr.add(self.processed_len),
							ptr.add(self.processed_len - self.deleted_count),
							self.original_len - self.processed_len,
						);
					}
				}
				
				// Safety: after filling holes, all items are in contiguous memory.
				unsafe {
					let len = self.original_len - self.deleted_count;
					VecInner::len(self.inner_ptr).write(len);
					*self.outer_len = len;
				}
			}
		}
		
		let mut g: DropGuard<S::T> = DropGuard {
			inner_ptr: self.inner_ptr(),
			outer_len: len,
			processed_len: 0,
			deleted_count: 0,
			original_len,
			_t: PhantomData
		};
		
		unsafe fn process_loop<T, const DELETED: bool>(
			DropGuard { inner_ptr, processed_len, deleted_count, original_len, .. }: &mut DropGuard<T>,
			keep: &mut impl FnMut(&mut T) -> bool,
		) {
			let ptr = VecInner::store(*inner_ptr).cast::<T>().as_ptr();
			
			while processed_len != original_len {
				// Safety: element within original length must be valid.
				let elem = &mut *ptr.add(*processed_len);
				
				let cur_len = *processed_len;
				*processed_len += 1;
				if !keep(elem) {
					*deleted_count += 1;

					// Safety: the vector holds a unique reference, and we never
					//  touch this element again after dropping it.
					ptr::drop_in_place(elem);
					
					if DELETED { continue } else { break }
				}
				
				// Safety: `deleted_count` > 0, so the hole slot must not overlap
				//  with the current element. The element is moved, then never
				//  touched again. The vector holds a unique reference.
				let hole_slot = ptr.add(cur_len - *deleted_count);
				ptr::copy_nonoverlapping(elem, hole_slot, 1);
			}
		}

		// Stage 1: nothing deleted
		process_loop::<_, false>(&mut g, &mut keep);
		// Stage 2: some elements deleted
		process_loop::<_, true >(&mut g, &mut keep);
		
		// Set the length.
		drop(g);
	}
	/// Removes elements for which `keep` returns `false` by truncation only. If the operation
	/// creates holes, the vector is not modified.
	#[allow(clippy::impl_trait_in_params, reason = "private API")]
	#[allow(clippy::mem_forget)]
	#[allow(clippy::multiple_unsafe_ops_per_block)]
	#[track_caller]
	pub fn retain_shared(&mut self, len: &mut usize, mut keep: impl FnMut(&S::T) -> bool) -> Result<(), Shared> {
		let original_len = *len;

		// Avoid double drop if the drop guard is not executed, since we may
		// make some holes during the process.
		*len = 0;

		// This drop guard will be invoked if `keep` panics, or if a hole would
		// be created in the vector. This reverts the length back to its original
		// value, leaving the vector unmodified. In cases when `keep` never
		// panics, it will be skipped.
		struct DropGuard<'a> {
			len: &'a mut usize,
			original_len: usize,
		}
		
		impl Drop for DropGuard<'_> {
			fn drop(&mut self) {
				*self.len = self.original_len;
			}
		}
		
		let mut processed_len = 0;
		let mut deleted_count = 0;
		let g = DropGuard { len, original_len };
		while processed_len != original_len {
			// Safety: element within original length must be valid.
			let elem = unsafe {
				self.ptr().add(processed_len).as_ref()
			};
			
			let deleted = deleted_count > 0;
			
			processed_len += 1;
			#[allow(clippy::else_if_without_else)]
			if !keep(elem) {
				deleted_count += 1;
				
				if deleted {
					break
				} else {
					continue
				}
			} else if deleted {
				// Hole detected!
				return Err(Shared(()))
			}
		}

		// No holes were created in the shared vector, only a possible truncation. Skip the guard's
		// dropper and truncate.
		mem::forget(g);
		// Safety: this is a simple truncation. All elements within this length remain valid.
		*len = original_len - deleted_count;
		Ok(())
	}

	/// Removes duplicate elements according to `equivalent`.
	///
	/// # Safety
	///
	/// The vector must be unique or contain one or zero elements.
	#[allow(clippy::impl_trait_in_params, reason = "private API")]
	#[allow(clippy::mem_forget)]
	#[allow(clippy::multiple_unsafe_ops_per_block)]
	#[track_caller]
	pub unsafe fn dedup_by_mutable(
		&mut self,
		len: &mut usize,
		mut equivalent: impl FnMut(&mut S::T, &mut S::T) -> bool
	) {
		let mut first_duplicate_idx = 1;
		let start = self.ptr();
		while first_duplicate_idx != *len {
			// The subtraction cannot overflow because we start the index at 1.
			// Safety: the index is always within the range `[1,len)`.
			let mut prev = start.add(first_duplicate_idx.wrapping_sub(1));
			let mut curr = start.add(first_duplicate_idx);
			if equivalent(curr.as_mut(), prev.as_mut()) {
				break
			}
			
			first_duplicate_idx += 1;
		}
		
		// No duplicates found. Nothing to do.
		if first_duplicate_idx == *len {
			return
		}

		// The outer length may have fallen out of sync with the inner length,
		// which would cause elements to be lost without dropping after modifying.
		// To prevent this, these elements first need to be dropped.
		// This is placed *after* the duplicate check to avoid inner truncation
		// on a shared vector with a single element.
		self.truncate(*len);

		struct DropGuard<'a, T> {
			inner_ptr: NonNull<VecInner<()>>,
			outer_len: &'a mut usize,
			// Position of the element to check.
			read: usize,
			// Position to write non-duplicates.
			write: usize,
			_t: PhantomData<&'a mut T>,
		}
		
		impl<T> Drop for DropGuard<'_, T> {
			fn drop(&mut self) {
				// Safety: the invariants `read >= write` and `len >= read` are upheld, and the copy
				//  is always in-bounds.
				unsafe {
					let ptr = VecInner::store(self.inner_ptr).cast::<T>().as_ptr();
					let len = *self.outer_len;

					// The number of elements left when `equivalent` panics
					let remaining_len = len.wrapping_sub(self.read);
					// The first dropped element
					let dropped_ptr = ptr.add(self.write);
					// The first unchecked element
					let valid_ptr = ptr.add(self.read);

					// Shift remaining unchecked elements back to fill the hole
					// left behind when `equivalent` panicked.
					ptr::copy(valid_ptr, dropped_ptr, remaining_len);

					// The number of elements which have already been dropped
					let dropped_len = self.read.wrapping_sub(self.write);
					
					let new_len = len - dropped_len;
					*self.outer_len = new_len;
					VecInner::len(self.inner_ptr).write(new_len);
				}
			}
		}

		// Construct a gap for the first duplicate and drop it, to avoid memory corruption if `drop`
		// panics.
		let mut gap = DropGuard {
			inner_ptr: self.inner_ptr(),
			outer_len: len,
			read: first_duplicate_idx + 1,
			write: first_duplicate_idx,
			_t: PhantomData::<&mut S::T>
		};
		// Safety: the branch above ensures `first_duplicate_idx` is within bounds. If it were
		//  greater than the length, the branch returns. If `drop` panics, the drop guard safely
		//  removes this element without dropping.
		ptr::drop_in_place(start.add(first_duplicate_idx).as_ptr());

		// Safety: `read_ptr`, `prev_ptr`, and `write_ptr` are always in-bounds and
		//  `read_ptr` never aliases `prev_ptr`.
		while gap.read < *gap.outer_len {
			let mut read_ptr = start.add(gap.read);
			let mut prev_ptr = start.add(gap.write.wrapping_sub(1));
			
			if equivalent(read_ptr.as_mut(), prev_ptr.as_mut()) {
				// Increment `read` first since the drop may panic.
				gap.read += 1;
				// Drop the duplicate in-place.
				ptr::drop_in_place(read_ptr.as_ptr());
			} else {
				let write_ptr = start.add(gap.write);

				// `read_ptr != write_ptr` because we've skipped at least one
				// element before the loop.
				ptr::copy_nonoverlapping(read_ptr.as_ptr(), write_ptr.as_ptr(), 1);

				// This position is filled, increment.
				gap.write += 1;
				gap.read += 1;
			}
		}
		
		let written_len = gap.write;
		mem::forget(gap);
		self.set_len(len, written_len);
	}
	/// Removes duplicate elements according to `equivalent`. If duplicates occur at the end, they
	/// are removed by truncation. Otherwise, an error is returned.
	pub fn dedup_by_shared(
		&mut self,
		len: &mut usize,
		mut equivalent: impl FnMut(&S::T, &S::T) -> bool
	) -> Result<(), Shared> {
		if *len < 2 {
			return Ok(())
		}
		
		// Safety: the length is passed by the outer vector.
		let slice = unsafe { self.as_slice(*len) };
		let Some(first_duplicate_idx) =
			slice[1..]
				.iter()
				.enumerate()
				.position(|(i, cur)|
					equivalent(cur, &slice[i - 1])
				)
		else {
			// No duplicates found
			return Ok(())
		};

		// Check if all consecutive elements are duplicates. Return early if any
		// non-equal element is found, as we can't shift back in a shared vector.
		if first_duplicate_idx < slice.len() {
			for i in first_duplicate_idx + 1..slice.len() {
				if !equivalent(&slice[i], &slice[i - 1]) {
					return Err(Shared(()))
				}
			}
		}

		// Safety: elements up to this index are untouched, so remain valid; this
		//  is a truncation.
		*len = first_duplicate_idx;
		Ok(())
	}

	/// Pushes `value` to the vector.
	///
	/// # Safety
	///
	/// The vector must have sufficient capacity for the pushed value, and must be unique.
	pub unsafe fn push_unchecked(&mut self, len: &mut usize, value: S::T) {
		self.ptr().add(*len).write(value);
		self.set_len(len, *len + 1);
	}

	/// Pops the last element from the vector.
	///
	/// # Safety
	///
	/// The vector must not be empty, and must be unique.
	pub unsafe fn pop_unchecked(&mut self, len: &mut usize) -> S::T {
		let idx = *len - 1;
		let value = self.ptr().add(idx).read();
		self.set_len(len, idx);
		value
	}
	
	/// Appends slice(s) from another vector to this vector by cloning, clearing the source vector.
	/// 
	/// # Safety
	/// 
	/// The length of the source vector must not overflow the capacity of the target vector
	/// (`self`). The target vector must be unique and non-dangling.
	#[allow(clippy::impl_trait_in_params, reason = "private API")]
	#[track_caller]
	pub unsafe fn append_shared(&mut self, target_len: &mut usize, source: &mut (impl VecTrait<S::T> + ?Sized))
	where
		S::T: Clone
	{
		struct DropGuard<T> {
			ptr: NonNull<T>,
			len: usize
		}

		impl<T> Drop for DropGuard<T> {
			#[track_caller]
			fn drop(&mut self) {
				let &mut Self { ptr, len } = self;
				// Safety: `len` elements have been cloned into the vector at `ptr`.
				unsafe {
					let slice = NonNull::slice_from_raw_parts(ptr, len);
					ptr::drop_in_place(slice.as_ptr());
				}
			}
		}

		let mut len = *target_len;

		// Drop the already cloned elements if `T::clone` panics.
		let mut guard = DropGuard {
			ptr: self.ptr().add(len),
			len: 0
		};
		
		for elem in source.slices().flatten() {
			let ptr = guard.ptr.add(guard.len);
			ptr.write(elem.clone());
			guard.len += 1;
		}

		// Don't drop elements
		mem::forget(guard);

		source.clear();
		// Safety: `source.len()` elements have been cloned to the target vector.
		self.set_len(target_len, len);
	}

	/// Appends slice(s) from another vector to this vector by moving its contents, clearing the
	/// source vector.
	///
	/// # Safety
	///
	/// The length of the source vector must not overflow the capacity of the target vector
	/// (`self`). The target vector must be unique and non-dangling.
	#[allow(clippy::impl_trait_in_params, reason = "private API")]
	pub unsafe fn append_unique(&mut self, target_len: &mut usize, source: &mut (impl VecTrait<S::T> + ?Sized)) {
		let mut len = *target_len;
		// The second copy will be unrolled and optimized away if the source
		// collection is not a deque.
		for slice in source.slices() {
			let target = self.ptr().add(len);

			// Safety: The memory can't possibly overlap, as this would require
			//  both to hold a shared reference, which is not allowed. All elements
			//  up to `len` in `other` are valid.
			ptr::copy_nonoverlapping(slice.as_ptr(), target.as_ptr(), slice.len());
			len += slice.len();
		}

		// Safety: all elements have been moved to the target vector.
		source.set_len(0);
		source.clear(); // Reset head
		// Safety: `source.len()` elements have been written to the target vector.
		self.set_len(target_len, len);
	}

	/// Extends the vector with elements from `iter`.
	///
	/// # Safety
	///
	/// `iter` must not overflow the vector capacity. The vector must be unique.
	#[allow(clippy::impl_trait_in_params, reason = "private API")]
	#[track_caller]
	pub unsafe fn extend_trusted(&mut self, len: &mut usize, iter: impl IntoIterator<Item = S::T>) {
		for v in iter {
			self.push_unchecked(len, v);
		}
	}

	/// Extends the vector with `count` elements returned from `fill`.
	///
	/// # Safety
	///
	/// The vector must have sufficient capacity for `count` elements. It must be unique.
	#[allow(clippy::impl_trait_in_params, reason = "private API")]
	#[track_caller]
	pub unsafe fn extend_with(&mut self, len: &mut usize, count: usize, mut fill: impl FnMut() -> S::T) {
		// We don't extend with `repeat_with` because the closure could panic,
		// cluttering the backtrace.
		for _ in 0..count {
			self.push_unchecked(len, fill());
		}
	}

	/// Extends the vector with `count` clones of `value`.
	///
	/// # Safety
	///
	/// The vector must have sufficient capacity for `count` elements. It must be unique.
	#[track_caller]
	pub unsafe fn extend_repeated(&mut self, len: &mut usize, count: usize, value: S::T)
	where
		S::T: Clone
	{
		// We don't extend with `repeat` because `clone` could panic, cluttering the backtrace.
		for _ in 0..count {
			self.push_unchecked(len, value.clone());
		}
	}

	/// Extends the vector with a clone of a slice within the vector.
	///
	/// # Safety
	///
	/// `range` must be within bounds. The vector must have sufficient capacity for the slice. It
	/// must be unique.
	#[track_caller]
	pub unsafe fn extend_from_within(&mut self, len: &mut usize, range: Range<usize>)
	where
		S::T: Clone
	{
		// Safety: `range` is within bounds.
		let ptr = self.ptr().add(range.start);
		let slice = NonNull::slice_from_raw_parts(ptr, range.len());
		self.extend_from_slice(len, slice);
	}

	/// Extends the vector with a clone of `slice`.
	///
	/// # Safety
	///
	/// The vector must have sufficient capacity for the `slice`. It must be unique.
	#[track_caller]
	pub unsafe fn extend_from_slice(&mut self, len: &mut usize, slice: NonNull<[S::T]>)
	where
		S::T: Clone
	{
		struct SetLenOnDrop<'a> {
			outer_len: &'a mut usize,
			inner_len: NonNull<usize>,
			len: usize,
		}

		impl Drop for SetLenOnDrop<'_> {
			fn drop(&mut self) {
				// Safety: elements within `len` have been initialized.
				unsafe {
					*self.outer_len = self.len;
					self.inner_len.write(self.len);
				}
			}
		}

		let target = self.ptr();
		let mut guard = SetLenOnDrop {
			len: *len,
			outer_len: len,
			inner_len: VecInner::len(self.inner_ptr()),
		};

		let source = slice.cast::<S::T>();

		// Safety: elements within `slice.len` are valid.
		for i in 0..slice.len() {
			target.add(guard.len).write((*source.as_ptr().add(i)).clone());
			// Increment length *after*, in case `clone` panics.
			guard.len += 1;
		}
		
		// Set the length
		drop(guard);
	}
}
