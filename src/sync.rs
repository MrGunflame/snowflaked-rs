//! Thread-safe Snowflake Generator
//!
//! **Requires the `sync` feature to be enabled.**
//!
//! This module provides [`Generator`] which can safely be shared between threads. Its constructor
//! is also const allowing to use it in a `static` context.

use crate::{Snowflake, INSTANCE_MAX};

use std::sync::atomic::{AtomicU16, AtomicU64, Ordering};
use std::time::UNIX_EPOCH;

/// A generator for unique snowflake ids. Since [`generate`] accepts a `&self` reference this can
/// be used in a `static` context.
///
/// # Examples
/// ```
/// use snowflaked::sync::Generator;
///
/// static GENERATOR: Generator = Generator::new_unchecked(0);
///
/// fn generate_id() -> u64 {
///     GENERATOR.generate()
/// }
/// ```
///
/// [`generate`]: Self::generate
#[derive(Debug)]
pub struct Generator {
    instance: u16,
    sequence: AtomicU16,
    timestamp: AtomicU64,
}

impl Generator {
    /// Creates a new `Generator` using the given `instance`.
    ///
    /// # Panics
    ///
    /// Panics if `instance` exceeds the maximum value (2^10 - 1).
    pub fn new(instance: u16) -> Self {
        Self::new_checked(instance).expect("instance is too big for snowflake generator")
    }

    /// Creates a new `Generator` using the given `instance`. Returns `None` if the instance
    /// exceeds the maximum instance value (2^10 - 1).
    pub const fn new_checked(instance: u16) -> Option<Self> {
        if instance > INSTANCE_MAX {
            None
        } else {
            Some(Self::new_unchecked(instance))
        }
    }

    /// Creates a new `Generator` using the given `instance` without checking if it exceeds the
    /// maximum value (2^10 - 1).
    ///
    /// Note: If `instance` exceeds the maximum value the `Generator` will create incorrect
    /// snowflakes.
    pub const fn new_unchecked(instance: u16) -> Self {
        Self {
            instance,
            sequence: AtomicU16::new(instance),
            timestamp: AtomicU64::new(0),
        }
    }

    /// Generate a new unique snowflake id.
    pub fn generate<T>(&self) -> T
    where
        T: Snowflake,
    {
        let mut sequence = self.sequence.load(Ordering::Acquire);
        sequence = (sequence + 1) % 4096;
        self.sequence.store(sequence, Ordering::Release);

        let mut timestamp = self.timestamp.load(Ordering::Acquire);
        loop {
            let new_timestamp = UNIX_EPOCH.elapsed().unwrap().as_millis() as u64;

            if sequence != 0 || new_timestamp > timestamp {
                timestamp = new_timestamp;
                self.timestamp.store(timestamp, Ordering::Release);
                break;
            }

            std::hint::spin_loop();
        }

        T::from_parts(timestamp, self.instance as u64, sequence as u64)
    }
}

impl Clone for Generator {
    fn clone(&self) -> Self {
        let sequence = self.sequence.load(Ordering::Relaxed);
        let timestamp = self.timestamp.load(Ordering::Relaxed);

        Self {
            instance: self.instance,
            sequence: AtomicU16::new(sequence),
            timestamp: AtomicU64::new(timestamp),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::sync::atomic::Ordering;

    use super::Generator;
    use crate::Snowflake;

    #[test]
    fn test_generate() {
        const INSTANCE: u64 = 0;

        let mut sequence = 1;
        let generator = Generator::new_unchecked(INSTANCE as u16);

        for _ in 0..10_000 {
            let id: u64 = generator.generate();
            assert_eq!(id.instance(), INSTANCE);
            assert_eq!(id.sequence(), sequence);

            match sequence {
                4095 => sequence = 0,
                _ => sequence += 1,
            }
        }
    }

    #[test]
    fn test_generate_no_duplicates() {
        let generator = Generator::new_unchecked(0);
        let mut ids: Vec<u64> = Vec::with_capacity(10_000);

        for _ in 0..ids.capacity() {
            ids.push(generator.generate());
        }

        for (index, id) in ids.iter().enumerate() {
            for (index2, id2) in ids.iter().enumerate() {
                if index != index2 {
                    if id == id2 {
                        panic!(
                            "Found duplicate id {} at index {} and {}",
                            id, index, index2
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn test_generator_clone() {
        let generator = Generator::new_unchecked(0);

        let cloned = generator.clone();

        assert_eq!(generator.instance, cloned.instance);
        assert_eq!(
            generator.sequence.load(Ordering::Relaxed),
            cloned.sequence.load(Ordering::Relaxed),
        );
        assert_eq!(
            generator.sequence.load(Ordering::Relaxed),
            cloned.sequence.load(Ordering::Relaxed),
        );
    }
}
