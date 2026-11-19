// Copyright (c) 2026 Mohammad Mahdi Abdollahpour.
// SPDX-License-Identifier: CPAL-1.0
// The contents of this file are subject to the Common Public Attribution
// License Version 1.0 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// https://opensource.org/license/cpal-1-0.
// The Original Code is mpmc-lean. The Initial Developer is Mohammad Mahdi
// Abdollahpour. See LICENSE and NOTICE.

#![allow(missing_docs)]

use std::collections::VecDeque;
use std::sync::atomic::{AtomicU8, AtomicUsize, Ordering};
use std::sync::{Arc, Barrier};
use std::thread;
use std::time::{Duration, Instant};

use mpmc_lean::{CreateError, PushError, Queue, MAX_CAPACITY, MIN_CAPACITY};

fn backoff(spins: &mut u32) {
    if *spins % 64 == 0 {
        std::thread::yield_now();
    } else {
        std::hint::spin_loop();
    }
    *spins = spins.wrapping_add(1);
}

#[test]
fn queue_reports_capacity_and_fifo() {
    let queue = Queue::new(4).expect("create queue");
    assert_eq!(queue.capacity(), 4);

    for value in 0..4 {
        queue.push(value).expect("space");
    }
    assert_eq!(queue.push(4), Err(PushError::Full));

    for value in 0..4 {
        assert_eq!(queue.pop(), Some(value));
    }
    assert_eq!(queue.pop(), None);
}

#[test]
fn queue_round_trips_edge_values() {
    let queue = Queue::new(2).expect("create queue");
    queue.push(0).expect("space");
    queue.push(u64::MAX).expect("space");
    assert_eq!(queue.pop(), Some(0));
    assert_eq!(queue.pop(), Some(u64::MAX));
    assert_eq!(queue.pop(), None);
}

#[test]
fn dropping_queue_with_queued_values_is_safe() {
    let queue = Queue::new(4).expect("create queue");
    for value in 0..4 {
        queue.push(value).expect("space");
    }
    drop(queue);
}

#[test]
fn randomized_sequential_matches_vecdeque() {
    let queue = Queue::new(4).expect("create queue");
    let mut reference = VecDeque::new();

    // Explicitly exercise a full queue and an empty pop before randomizing.
    for value in [11, 22, 33, 44] {
        assert_eq!(queue.push(value), Ok(()));
        reference.push_back(value);
    }
    assert_eq!(queue.push(55), Err(PushError::Full));
    while let Some(expected) = reference.pop_front() {
        assert_eq!(queue.pop(), Some(expected));
    }
    assert_eq!(queue.pop(), None);

    // These counters cover only the randomized phase below.
    let mut max_depth = 0;
    let mut full_events = 0;
    let mut empty_events = 0;
    let mut state = 0x9e37_79b9_7f4a_7c15_u64;
    for _ in 0..50_000 {
        state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        if state >> 63 == 0 {
            if reference.len() == 4 {
                assert_eq!(queue.push(state), Err(PushError::Full));
                full_events += 1;
            } else {
                assert_eq!(queue.push(state), Ok(()));
                reference.push_back(state);
                max_depth = max_depth.max(reference.len());
            }
        } else if let Some(expected) = reference.pop_front() {
            assert_eq!(queue.pop(), Some(expected));
        } else {
            assert_eq!(queue.pop(), None);
            empty_events += 1;
        }
    }

    while let Some(expected) = reference.pop_front() {
        assert_eq!(queue.pop(), Some(expected));
    }
    assert_eq!(queue.pop(), None);
    assert!(full_events > 0);
    assert!(empty_events > 0);
    assert_eq!(max_depth, 4);
}

#[test]
fn invalid_capacities_are_rejected() {
    for capacity in [0, 1, 3, MAX_CAPACITY + 1, usize::MAX] {
        assert_eq!(
            Queue::new(capacity).map(|_| ()),
            Err(CreateError::InvalidCapacity(capacity))
        );
    }
    assert_eq!(MIN_CAPACITY, 2);
}

fn assert_send_sync<T: Send + Sync>() {}

#[test]
fn queue_is_send_and_sync() {
    assert_send_sync::<Queue>();
}

#[test]
fn concurrent_exactly_once_delivery() {
    const PRODUCERS: usize = 4;
    const CONSUMERS: usize = 4;
    const PER_PRODUCER: usize = 10_000;
    const TOTAL: usize = PRODUCERS * PER_PRODUCER;

    let queue = Arc::new(Queue::new(2).expect("create queue"));
    let seen = Arc::new(
        (0..TOTAL)
            .map(|_| AtomicU8::new(0))
            .collect::<Vec<AtomicU8>>(),
    );
    let consumed = Arc::new(AtomicUsize::new(0));
    let start = Arc::new(Barrier::new(PRODUCERS + CONSUMERS));
    let deadline = Instant::now() + Duration::from_secs(20);

    let mut handles = Vec::with_capacity(PRODUCERS + CONSUMERS);

    for producer in 0..PRODUCERS {
        let queue = Arc::clone(&queue);
        let start = Arc::clone(&start);
        handles.push(thread::spawn(move || {
            start.wait();
            for index in 0..PER_PRODUCER {
                let value = ((producer as u64) << 32) | index as u64;
                let mut spins = 0;
                loop {
                    match queue.push(value) {
                        Ok(()) => break,
                        Err(_) => {
                            assert!(
                                Instant::now() < deadline,
                                "producer {producer} timed out waiting for space"
                            );
                            backoff(&mut spins);
                        }
                    }
                }
            }
        }));
    }

    for _ in 0..CONSUMERS {
        let queue = Arc::clone(&queue);
        let seen = Arc::clone(&seen);
        let consumed = Arc::clone(&consumed);
        let start = Arc::clone(&start);
        handles.push(thread::spawn(move || {
            start.wait();
            let mut last_seen: [Option<u64>; PRODUCERS] = [None; PRODUCERS];
            let mut spins = 0;
            loop {
                match queue.pop() {
                    Some(value) => {
                        let producer = (value >> 32) as usize;
                        let index = (value & 0xffff_ffff) as usize;
                        assert!(producer < PRODUCERS);
                        assert!(index < PER_PRODUCER);
                        if let Some(previous) = last_seen[producer] {
                            assert!(
                                index as u64 > previous,
                                "producer {producer} was reordered: {previous} after {index}"
                            );
                        }
                        last_seen[producer] = Some(index as u64);

                        let slot = producer * PER_PRODUCER + index;
                        let previous = seen[slot].fetch_add(1, Ordering::SeqCst);
                        assert_eq!(previous, 0, "value {value:#x} delivered twice");

                        let count = consumed.fetch_add(1, Ordering::SeqCst) + 1;
                        if count == TOTAL {
                            break;
                        }
                    }
                    None => {
                        if consumed.load(Ordering::SeqCst) == TOTAL {
                            break;
                        }
                        assert!(Instant::now() < deadline, "consumer timed out");
                        backoff(&mut spins);
                    }
                }
            }
        }));
    }

    for handle in handles {
        handle.join().expect("worker panicked");
    }

    for (index, count) in seen.iter().enumerate() {
        assert_eq!(count.load(Ordering::SeqCst), 1, "value {index} was lost");
    }
    assert_eq!(consumed.load(Ordering::SeqCst), TOTAL);
    assert_eq!(queue.pop(), None, "queue was not empty after delivery");
}

#[test]
fn single_consumer_preserves_per_producer_order() {
    const PRODUCERS: usize = 4;
    const PER_PRODUCER: usize = 5_000;
    const TOTAL: usize = PRODUCERS * PER_PRODUCER;

    let queue = Arc::new(Queue::new(2).expect("create queue"));
    let start = Arc::new(Barrier::new(PRODUCERS + 1));
    let deadline = Instant::now() + Duration::from_secs(20);
    let mut handles = Vec::with_capacity(PRODUCERS);

    for producer in 0..PRODUCERS {
        let queue = Arc::clone(&queue);
        let start = Arc::clone(&start);
        handles.push(thread::spawn(move || {
            start.wait();
            let mut spins = 0;
            for index in 0..PER_PRODUCER {
                let value = ((producer as u64) << 32) | index as u64;
                loop {
                    match queue.push(value) {
                        Ok(()) => break,
                        Err(_) => {
                            assert!(Instant::now() < deadline, "producer timed out");
                            backoff(&mut spins);
                        }
                    }
                }
            }
        }));
    }

    start.wait();
    let mut next = [0usize; PRODUCERS];
    let mut spins = 0;
    for _ in 0..TOTAL {
        loop {
            if let Some(value) = queue.pop() {
                let producer = (value >> 32) as usize;
                let index = (value & 0xffff_ffff) as usize;
                assert!(producer < PRODUCERS);
                assert_eq!(index, next[producer], "producer {producer} was reordered");
                next[producer] += 1;
                break;
            }
            assert!(Instant::now() < deadline, "consumer timed out");
            backoff(&mut spins);
        }
    }

    for handle in handles {
        handle.join().expect("producer panicked");
    }
    assert_eq!(next, [PER_PRODUCER; PRODUCERS]);
    assert_eq!(queue.pop(), None);
}

#[test]
fn mixed_push_pop_threads_preserve_values() {
    const THREADS: usize = 4;
    const PUSHES: usize = 5_000;
    const OPS: usize = 20_000;

    let queue = Arc::new(Queue::new(8).expect("create queue"));
    let seen = Arc::new(
        (0..THREADS * PUSHES)
            .map(|_| AtomicU8::new(0))
            .collect::<Vec<AtomicU8>>(),
    );
    let start = Arc::new(Barrier::new(THREADS));
    let deadline = Instant::now() + Duration::from_secs(20);
    let mut handles = Vec::with_capacity(THREADS);

    for thread_id in 0..THREADS {
        let queue = Arc::clone(&queue);
        let seen = Arc::clone(&seen);
        let start = Arc::clone(&start);
        handles.push(thread::spawn(move || {
            start.wait();
            let mut pushed = 0;
            let mut spins = 0;

            for op in 0..OPS {
                if op % 4 == 0 {
                    let slot = thread_id * PUSHES + pushed;
                    let value = ((thread_id as u64) << 32) | pushed as u64;
                    // Mark before publication: a consumer may pop the value
                    // immediately after a successful push returns.
                    seen[slot].store(1, Ordering::SeqCst);
                    loop {
                        match queue.push(value) {
                            Ok(()) => {
                                pushed += 1;
                                break;
                            }
                            Err(_) => {
                                if let Some(other) = queue.pop() {
                                    mark_consumed(&seen, other, THREADS, PUSHES);
                                }
                                assert!(Instant::now() < deadline, "push timed out");
                                backoff(&mut spins);
                            }
                        }
                    }
                } else if let Some(value) = queue.pop() {
                    mark_consumed(&seen, value, THREADS, PUSHES);
                } else {
                    assert!(Instant::now() < deadline, "pop timed out");
                    backoff(&mut spins);
                }
            }

            assert_eq!(pushed, PUSHES);
        }));
    }

    for handle in handles {
        handle.join().expect("worker panicked");
    }

    while let Some(value) = queue.pop() {
        mark_consumed(&seen, value, THREADS, PUSHES);
    }
    for (slot, state) in seen.iter().enumerate() {
        assert_eq!(state.load(Ordering::SeqCst), 2, "value {slot} was lost");
    }
    assert_eq!(queue.pop(), None);
}

fn mark_consumed(seen: &[AtomicU8], value: u64, threads: usize, pushes: usize) {
    let thread_id = (value >> 32) as usize;
    let index = (value & 0xffff_ffff) as usize;
    assert!(thread_id < threads);
    assert!(index < pushes);
    let slot = thread_id * pushes + index;
    let previous = seen[slot].swap(2, Ordering::SeqCst);
    assert_eq!(previous, 1, "value {value:#x} was duplicated or unseen");
}
