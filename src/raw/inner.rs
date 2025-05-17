// Copyright 2025 - Strixpyrr
// SPDX-License-Identifier: Apache-2.0

use alloc::alloc::alloc;
use core::alloc::{Allocator, Layout};
use core::mem::{align_of_val_raw, size_of_val_raw};
use core::{cmp, hint, mem, ptr};
use core::ptr::{metadata, NonNull, Pointee};
use crate::raw::VecInner;
use super::{check_size, AllocError};

/// A raw vector abstracted away from generic types, except the allocator. All vector and deque
/// types may use this type. The layout of the inner buffer must be passed to all methods.
/// 
/// Unlike the standard library's [`RawVecInner`](alloc::raw_vec::RawVecInner), the capacity is
/// handled by the outer vector. This is because both fixed-capacity and dynamic-capacity vectors
/// may use this type.
pub struct RawInnerVec<A> {
	ptr: InnerVecPtr,
	alloc: A,
}

#[derive(Copy, Clone)]
enum InnerVecPtr {
	Dangling,
	Allocated {
		ptr: NonNull<u8>
	}
}

impl<A: Allocator + Clone> Clone for RawInnerVec<A> {
	fn clone(&self) -> Self {
		Self {
			ptr: self.ptr,
			alloc: self.alloc.clone(),
		}
	}
}

impl<A: Allocator> RawInnerVec<A> {
	const MAX_CAP: usize = isize::MAX as usize;
	
	pub const fn dangling(alloc: A) -> Self {
		Self {
			ptr: InnerVecPtr::Dangling,
			alloc,
		}
	}
	
	#[track_caller]
	pub fn with_capacity(cap: usize, alloc: A, base_layout: Layout, elem_layout: Layout) -> Self {
		match Self::try_with_capacity(cap, alloc, base_layout, elem_layout) {
			Ok(this) => this,
			Err(err) => err.handle()
		}
	}
	
	pub fn try_with_capacity(
		cap: usize,
		alloc: A,
		base_layout: Layout,
		elem_layout: Layout,
	) -> Result<Self, AllocError> {
		if cap == 0 {
			return Ok(Self::dangling(alloc))
		}
		
		let layout = inner_layout(base_layout, elem_layout, cap)?;
		Self::allocate(layout, alloc)
	}

	pub fn allocate(layout: Layout, alloc: A) -> Result<Self, AllocError> {
		check_size(layout.size())?;

		let ptr = match alloc.allocate(layout) {
			Ok(ptr) => ptr.cast::<u8>(),
			Err(_) => return Err(AllocError::Alloc { layout })
		};

		Ok(Self {
			ptr: InnerVecPtr::Allocated { ptr },
			alloc,
		})
	}
	
	pub unsafe fn from_raw_parts(ptr: *mut u8, alloc: A) -> Self {
		Self::from_non_null(NonNull::new_unchecked(ptr), alloc)
	}

	pub unsafe fn from_non_null(ptr: NonNull<u8>, alloc: A) -> Self {
		Self {
			ptr: InnerVecPtr::Allocated { ptr },
			alloc,
		}
	}
	
	pub fn is_dangling(&self) -> bool {
		matches!(self.ptr, InnerVecPtr::Dangling)
	}
	
	/// Gets the element pointer, offset by a `prefix` layout.
	pub fn ptr<T>(&self, prefix: Layout) -> NonNull<T> {
		match self.ptr {
			InnerVecPtr::Dangling => NonNull::dangling(),
			InnerVecPtr::Allocated { ptr } =>
				// Safety: `ptr` points to allocated memory, and the prefix always
				//  fits in `isize`.
				unsafe {
					ptr.byte_add(prefix.size()).cast()
				}
		}
	}
	
	/// Casts the inner pointer.
	pub fn inner_ptr<T>(&self) -> NonNull<T> {
		match self.ptr {
			InnerVecPtr::Dangling => NonNull::dangling(),
			InnerVecPtr::Allocated { ptr } => ptr.cast(),
		}
	}
	
	/// Casts the inner pointer with an associated length.
	/// 
	/// # Safety
	/// 
	/// The total size of the type (sized prefix + slice tail) must fit in `isize`.
	pub unsafe fn inner_ptr_with_metadata<T>(&self, length: usize) -> NonNull<T>
	where
		T: Pointee<Metadata = usize> + ?Sized
	{
		let ptr = match self.ptr {
			InnerVecPtr::Dangling => {
				// We have to get creative to smuggle out the alignment, since `align_of` requires a
				// sized type. Since `align_of_val_raw` does *not* require a pointer valid for
				// dereferencing, we reconstruct the DST on a null pointer and get the alignment from
				// it.
				let null = ptr::from_raw_parts(ptr::null::<u8>(), length);
				debug_assert!(
					size_of_val_raw::<T>(null) <= isize::MAX as usize,
					"size should fit in `isize`"
				);
				// Safety: the slice length is initialized to `length`, and the caller promises that
				//  the total size fits `isize`.
				let alignment = align_of_val_raw::<T>(null);
				
				let byte_ptr = ptr::without_provenance_mut::<u8>(alignment);
				// Safety: alignment is always non-zero.
				NonNull::new_unchecked(byte_ptr)
			}
			InnerVecPtr::Allocated { ptr } => ptr
		};
		NonNull::from_raw_parts(ptr, length)
	}

	pub fn allocator(&self) -> &A {
		&self.alloc
	}
	
	fn current_memory(&self, cap: usize, base_layout: Layout, elem_layout: Layout) -> Option<(NonNull<u8>, Layout, usize)> {
		match self.ptr {
			InnerVecPtr::Dangling => None,
			InnerVecPtr::Allocated { ptr } =>
				// Safety: the memory is currently allocated, so we know that the layout cannot
				//  overflow `isize`.
				unsafe {
					let store_size = elem_layout.size().wrapping_mul(cap);
					let store_layout = Layout::from_size_align_unchecked(store_size, elem_layout.align());
					let (layout, elem_offset) = base_layout.extend(store_layout).unwrap_unchecked();
					Some((ptr, layout, elem_offset))
				}
		}
	}
	
	#[track_caller]
	pub fn reserve(
		&mut self,
		len: usize,
		cap: &mut usize,
		additional: usize,
		base_layout: Layout,
		elem_layout: Layout,
	) {
		#[cold]
		#[track_caller]
		fn reserve<A: Allocator>(
			this: &mut RawInnerVec<A>,
			len: usize,
			cap: &mut usize,
			additional: usize,
			base_layout: Layout,
			elem_layout: Layout,
		) {
			if let Err(err) = this.grow_amortized(len, cap, additional, base_layout, elem_layout) {
				err.handle();
			}
		}
		
		if self.must_grow(len, *cap, additional, elem_layout) {
			reserve(self, len, cap, additional, base_layout, elem_layout);
		}

		// Safety: this condition was checked above.
		unsafe {
			// Inform the optimizer that the vector is now large enough to hold the
			// additional elements.
			hint::assert_unchecked(!self.must_grow(len, *cap, additional, elem_layout));
		}
	}
	
	pub fn try_reserve(
		&mut self,
		len: usize,
		cap: &mut usize,
		additional: usize,
		base_layout: Layout,
		elem_layout: Layout,
	) -> Result<(), AllocError> {
		if self.must_grow(len, *cap, additional, elem_layout) {
			self.grow_amortized(len, cap, additional, base_layout, elem_layout)?;
		}
		
		// Safety: this condition was checked above.
		unsafe {
			// Inform the optimizer that the vector is now large enough to hold the
			// additional elements.
			hint::assert_unchecked(!self.must_grow(len, *cap, additional, elem_layout));
		}
		Ok(())
	}
	
	#[track_caller]
	pub fn reserve_exact(
		&mut self,
		len: usize,
		cap: &mut usize,
		additional: usize,
		base_layout: Layout,
		elem_layout: Layout,
	) {
		#[cold]
		#[track_caller]
		pub fn reserve_exact<A: Allocator>(
			this: &mut RawInnerVec<A>,
			len: usize,
			cap: &mut usize,
			additional: usize,
			base_layout: Layout,
			elem_layout: Layout,
		) {
			if let Err(err) = this.grow_exact(len, cap, additional, base_layout, elem_layout) {
				err.handle();
			}
		}
		
		if self.must_grow(len, *cap, additional, elem_layout) {
			reserve_exact(self, len, cap, additional, base_layout, elem_layout);
		}

		// Safety: this condition was checked above.
		unsafe {
			// Inform the optimizer that the vector is now large enough to hold the
			// additional elements.
			hint::assert_unchecked(!self.must_grow(len, *cap, additional, elem_layout));
		}
	}

	pub fn try_reserve_exact(
		&mut self,
		len: usize,
		cap: &mut usize,
		additional: usize,
		base_layout: Layout,
		elem_layout: Layout,
	) -> Result<(), AllocError> {
		if self.must_grow(len, *cap, additional, elem_layout) {
			self.grow_exact(len, cap, additional, base_layout, elem_layout)?;
		}

		// Safety: this condition was checked above.
		unsafe {
			// Inform the optimizer that the vector is now large enough to hold the
			// additional elements.
			hint::assert_unchecked(!self.must_grow(len, *cap, additional, elem_layout));
		}
		Ok(())
	}
	
	fn must_grow(&self, len: usize, cap: usize, additional: usize, elem_layout: Layout) -> bool {
		additional > cap.wrapping_sub(len)
	}
	
	unsafe fn set_ptr_and_cap(&mut self, ptr: NonNull<[u8]>, cap: &mut usize, elem_size: usize) {
		// Todo: do we need to add the element stride to the size?
		self.set_ptr(ptr.cast());
		*cap = ptr.len() / elem_size;
	}
	
	pub unsafe fn set_ptr(&mut self, ptr: NonNull<u8>) {
		self.ptr = InnerVecPtr::Allocated { ptr: ptr.cast() };
	}
	
	fn grow_amortized(
		&mut self,
		len: usize,
		cur_cap: &mut usize,
		additional: usize,
		base_layout: Layout,
		elem_layout: Layout
	) -> Result<(), AllocError> {
		if elem_layout.size() == 0 {
			// Since we return a capacity of `usize::MAX` when the element size is
			// zero, getting here means the vector is overfull.
			return Err(AllocError::CapacityOverflow)
		}
		
		let required = len.checked_add(additional).ok_or(AllocError::CapacityOverflow)?;
		// This cannot overflow since the maximum capacity is `isize::MAX`, which
		// would be `usize::MAX` when doubled.
		let cap = cmp::max(*cur_cap * 2, required);
		let cap = cmp::max(min_non_zero_cap(elem_layout.size()), cap);
		
		let new_layout = inner_layout(base_layout, elem_layout, cap)?;
		
		let ptr = finish_grow(
			new_layout,
			self.current_memory(*cur_cap, base_layout, elem_layout),
			self.allocator()
		)?;
		// Safety: `finish_grow` would have resulted in an overflow error if we tried to allocate
		//  more than `isize::MAX` items.
		unsafe {
			self.set_ptr_and_cap(ptr, cur_cap, elem_layout.size());
		}
		Ok(())
	}

	fn grow_exact(
		&mut self,
		len: usize,
		cur_cap: &mut usize,
		additional: usize,
		base_layout: Layout,
		elem_layout: Layout
	) -> Result<(), AllocError> {
		if elem_layout.size() == 0 {
			// Since we return a capacity of `usize::MAX` when the element size is
			// zero, getting here means the vector is overfull.
			return Err(AllocError::CapacityOverflow)
		}

		let cap = len.checked_add(additional).ok_or(AllocError::CapacityOverflow)?;
		
		let new_layout = inner_layout(base_layout, elem_layout, cap)?;

		let ptr = finish_grow(
			new_layout,
			self.current_memory(*cur_cap, base_layout, elem_layout),
			self.allocator()
		)?;
		// Safety: `finish_grow` would have resulted in an overflow error if we tried to allocate
		//  more than `isize::MAX` items.
		unsafe {
			self.set_ptr_and_cap(ptr, cur_cap, elem_layout.size());
		}
		Ok(())
	}
	
	#[track_caller]
	pub fn shrink(
		&mut self,
		cur_cap: &mut usize,
		new_cap: usize,
		base_layout: Layout,
		elem_layout: Layout,
	) {
		if let Err(err) = self.try_shrink(cur_cap, new_cap, base_layout, elem_layout) {
			err.handle();
		}
	}
	
	#[track_caller]
	pub fn try_shrink(
		&mut self,
		cur_cap: &mut usize,
		new_cap: usize,
		base_layout: Layout,
		elem_layout: Layout,
	) -> Result<(), AllocError> {
		assert!(new_cap <= *cur_cap, "tried to shrink to larger capacity");
		// Safety: the new capacity was just checked to be smaller than the current one.
		unsafe {
			self.shrink_unchecked(cur_cap, new_cap, base_layout, elem_layout)
		}
	}
	
	unsafe fn shrink_unchecked(
		&mut self,
		cur_cap: &mut usize,
		new_cap: usize,
		base_layout: Layout,
		elem_layout: Layout,
	) -> Result<(), AllocError> {
		let Some((ptr, layout, _)) = self.current_memory(*cur_cap, base_layout, elem_layout) else {
			return Ok(())
		};
		
		// Unlike alloc's vector, we can't deallocate when `new_cap == 0`, as the counts still need
		// to be stored and weak references could be preventing deallocation.
		// Todo: deallocate if no weak references exist and capacity is zero? If there are weak refs,
		//  set strong count to 0 and set pointer to dangle?
		
		// Safety: this cannot overflow since the capacity was larger before.
		let new_size = elem_layout.size().unchecked_mul(new_cap);
		let new_layout = Layout::from_size_align_unchecked(new_size, layout.align());
		
		// Safety: `ptr` is currently allocated with `layout`, and `new_layout` is smaller.
		let Ok(ptr) = self.alloc.shrink(ptr, layout, new_layout) else {
			return Err(AllocError::Alloc { layout: new_layout })
		};
		
		// Safety: the old pointer is now invalid.
		self.set_ptr_and_cap(ptr, cur_cap, elem_layout.size());
		Ok(())
	}
	
	pub fn deallocate(&mut self, cap: usize, base_layout: Layout, elem_layout: Layout) {
		let Some((ptr, layout, _)) = self.current_memory(cap, base_layout, elem_layout) else { return };
		self.ptr = InnerVecPtr::Dangling;
		// Safety: `ptr` is currently allocated with `layout`.
		unsafe {
			self.alloc.deallocate(ptr, layout);
		}
	}
	
	/// Copies the memory out of the reference into a new allocation, replacing the old one and
	/// returning a pointer to it.
	pub unsafe fn copy_out(
		&mut self,
		len: usize,
		cap: usize,
		base_layout: Layout,
		elem_layout: Layout,
	) -> Result<Option<NonNull<u8>>, AllocError> {
		let Some((source, layout, elem_offset)) = self.current_memory(cap, base_layout, elem_layout)
		else {
			return Ok(None)
		};
		
		let target = self.alloc
						 .allocate(layout)
						 .map_err(|_| AllocError::Alloc { layout })?;
		// Todo: account for the element stride in the copy length?
		// Safety: the memory at `target` was newly allocated, so cannot overlap with `source`.
		ptr::copy_nonoverlapping(
			source.add(elem_offset).as_ptr(),
			target.cast::<u8>().add(elem_offset).as_ptr(),
			len * elem_layout.size()
		);
		
		// Todo: set the capacity in case the allocator over-allocates.
		self.set_ptr(target.cast());
		Ok(Some(source))
	}
}

const fn min_non_zero_cap(size: usize) -> usize {
	if size == 1 {
		8
	} else if size <= 1024 {
		4
	} else {
		1
	}
}

fn inner_layout(base: Layout, elem: Layout, cap: usize) -> Result<Layout, AllocError> {
	let store_size = elem.size().checked_mul(cap).ok_or(AllocError::CapacityOverflow)?;
	let store_layout = Layout::from_size_align(store_size, elem.align())?;
	let (layout, _) = base.extend(store_layout)?;
	Ok(layout)
}

#[cold]
fn finish_grow<A: Allocator>(
	new_layout: Layout,
	current_memory: Option<(NonNull<u8>, Layout, usize)>,
	alloc: &A
) -> Result<NonNull<[u8]>, AllocError> {
	check_size(new_layout.size())?;
	
	let memory = match current_memory {
		Some((ptr, old_layout, _)) => {
			// Safety: `ptr` points to memory currently allocated in `alloc` with `old_layout`. The
			//  size of `new_layout` is strictly greater than that of `old_layout`.
			unsafe {
				alloc.grow(ptr, old_layout, new_layout)
			}
		}
		None => alloc.allocate(new_layout)
	};
	
	memory.map_err(|_| AllocError::Alloc { layout: new_layout })
}
