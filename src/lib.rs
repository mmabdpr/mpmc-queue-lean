// Copyright (c) 2026 Mohammad Mahdi Abdollahpour.
// SPDX-License-Identifier: CPAL-1.0
// The contents of this file are subject to the Common Public Attribution
// License Version 1.0 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// https://opensource.org/license/cpal-1-0.
// The Original Code is mpmc-lean. The Initial Developer is Mohammad Mahdi
// Abdollahpour. See LICENSE and NOTICE.

#![doc = include_str!("../docs/rust.md")]
#![deny(unsafe_op_in_unsafe_fn)]
#![warn(missing_docs)]
#![warn(rust_2018_idioms)]

use std::fmt;
use std::ptr::NonNull;

/// Smallest capacity accepted by [`Queue::new`].
pub const MIN_CAPACITY: usize = 2;

/// Largest capacity accepted by [`Queue::new`] (2^24 slots).
///
/// At this capacity the C implementation allocates about 2 GiB.
pub const MAX_CAPACITY: usize = 1 << 24;

/// Opaque C queue handle.  Its layout belongs to `src/mpmc.c`.
#[repr(C)]
struct mpmc_queue {
    _private: [u8; 0],
}

mod ffi {
    use super::mpmc_queue;

    extern "C" {
        pub fn mpmc_create(capacity: u64) -> *mut mpmc_queue;
        pub fn mpmc_destroy(q: *mut mpmc_queue);
        pub fn mpmc_push(q: *mut mpmc_queue, value: u64) -> bool;
        pub fn mpmc_pop(q: *mut mpmc_queue, value: *mut u64) -> bool;
    }
}

/// Error returned when a queue cannot be created.
#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CreateError {
    /// The requested capacity is not a power of two in
    /// `[MIN_CAPACITY, MAX_CAPACITY]`.
    InvalidCapacity(usize),
    /// The C runtime could not create the queue.
    ///
    /// This covers allocation failure and unsupported 16-byte atomics. The
    /// public C constructor reports both with the same `NULL` result, so
    /// this error does not distinguish them.
    Unavailable,
}

impl fmt::Display for CreateError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidCapacity(capacity) => write!(
                f,
                "capacity {capacity} is not a power of two in [{MIN_CAPACITY}, {MAX_CAPACITY}]"
            ),
            Self::Unavailable => f.write_str(
                "queue creation failed: allocation or required 16-byte atomics are unavailable",
            ),
        }
    }
}

impl std::error::Error for CreateError {}

/// Error returned when [`Queue::push`] cannot publish a value.
#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PushError {
    /// The queue is full, or its publication horizon has been reached.
    ///
    /// The public C API maps both cases to `false`; the horizon is
    /// practically unreachable.
    Full,
}

impl fmt::Display for PushError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("queue is full")
    }
}

impl std::error::Error for PushError {}

/// A bounded multi-producer, multi-consumer queue of `u64` values.
///
/// `Queue` is a safe ownership wrapper around the C ABI.  It is
/// `Send + Sync`; share it with [`std::sync::Arc`] for concurrent use.
/// Values are consumed in FIFO order.
///
/// The constructor allocates the queue.  `push` and `pop` never allocate;
/// on a platform with lock-free 16-byte atomics they do not take a lock or
/// make a syscall.  An individual call may retry after losing a race.  The C
/// implementation is designed to be lock-free, but no machine-checked
/// progress theorem is claimed; see the crate documentation for the exact
/// proof scope and trusted computing base.
///
/// # Destruction
///
/// Dropping the `Queue` is equivalent to `mpmc_destroy`: it requires that no
/// other thread is inside a queue operation.  Rust's borrow rules enforce
/// that requirement for all safe uses of this type.
pub struct Queue {
    inner: NonNull<mpmc_queue>,
    capacity: usize,
}

// SAFETY: the C queue supports concurrent push/pop from any threads, and
// `Queue` owns exactly one handle with no aliasing `&mut` access.
unsafe impl Send for Queue {}
// SAFETY: all public operations take `&self` and the C implementation is a
// multi-producer/multi-consumer queue.
unsafe impl Sync for Queue {}

impl Queue {
    /// Creates a queue with the requested capacity.
    ///
    /// `capacity` must be a power of two in
    /// `[MIN_CAPACITY, MAX_CAPACITY]`.  The queue is ready for concurrent
    /// use when this function returns.
    ///
    /// # Errors
    ///
    /// Returns [`CreateError::InvalidCapacity`] before calling C for an
    /// invalid capacity. Returns [`CreateError::Unavailable`] if the C
    /// constructor returns `NULL` (allocation failure or unsupported 16-byte
    /// atomics).
    pub fn new(capacity: usize) -> Result<Self, CreateError> {
        if !(MIN_CAPACITY..=MAX_CAPACITY).contains(&capacity) || !capacity.is_power_of_two() {
            return Err(CreateError::InvalidCapacity(capacity));
        }

        // SAFETY: capacity was checked against the C constructor's range and
        // the returned pointer is either null or an owned live queue.
        let pointer = unsafe { ffi::mpmc_create(capacity as u64) };
        let inner = NonNull::new(pointer).ok_or(CreateError::Unavailable)?;
        Ok(Self { inner, capacity })
    }

    /// Returns the queue's fixed capacity.
    #[must_use]
    pub fn capacity(&self) -> usize {
        self.capacity
    }

    /// Attempts to append `value`.
    ///
    /// This is non-blocking.  It returns [`PushError::Full`] when the queue
    /// has no space (or, in principle, when the publication horizon is
    /// reached).
    ///
    /// # Errors
    ///
    /// Returns [`PushError::Full`] if the value was not published.
    pub fn push(&self, value: u64) -> Result<(), PushError> {
        // SAFETY: `inner` is a live handle owned by `self`.  The C function
        // accepts any 64-bit value and does not retain the pointer.
        let pushed = unsafe { ffi::mpmc_push(self.inner.as_ptr(), value) };
        if pushed {
            Ok(())
        } else {
            Err(PushError::Full)
        }
    }

    /// Attempts to remove the oldest value.
    ///
    /// This is non-blocking.  It returns `None` when the queue is empty.
    #[must_use]
    pub fn pop(&self) -> Option<u64> {
        let mut value = 0;
        // SAFETY: `inner` is a live handle and `value` is a valid, writable
        // output slot for the duration of the call.
        let popped = unsafe { ffi::mpmc_pop(self.inner.as_ptr(), &mut value) };
        if popped {
            Some(value)
        } else {
            None
        }
    }
}

impl fmt::Debug for Queue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Queue")
            .field("capacity", &self.capacity)
            .finish_non_exhaustive()
    }
}

impl Drop for Queue {
    fn drop(&mut self) {
        // SAFETY: `self` is the unique owner of `inner`; no method can be
        // running because `drop` has exclusive access.
        unsafe { ffi::mpmc_destroy(self.inner.as_ptr()) };
    }
}
