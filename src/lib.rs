//! A crate for working with snowflake ids.
//!
//! Most notably this provides [`Snowflake`] for working with custom snowflake ids and
//! [`Generator`] creating new snowflake ids.
//!
//! # Custom snowflake ids
//!
//! Custom snowflake ids can be created with the [`Snowflake`] trait.
//!
//! # Example
//! ```
//! use snowflaked::Snowflake;
//!
//! struct UserId(u64);
//!
//! impl Snowflake for UserId {
//!     fn from_parts(timestamp: u64, instance: u64, sequence: u64) -> Self {
//!         Self(u64::from_parts(timestamp, instance, sequence))
//!     }
//!
//!     fn timestamp(&self) -> u64 {
//!         self.0.timestamp()
//!     }
//!
//!     fn instance(&self) -> u64 {
//!         self.0.instance()
//!     }
//!
//!     fn sequence(&self) -> u64 {
//!         self.0.sequence()
//!     }
//! }
//! ```
//!
//! # Generating snowflake ids
//!
//! [`Generator`] can be used to generate unique snowflake ids. Additionally [`sync::Generator`]
//! can be used when working with multiple threads (requires the `sync` feature).
//!
//! # Example
//! ```
//! let mut generator = Generator::new(0);
//! let id: u64 = generator.generate();
//! ```
//!
//! [`Generator::generate`] can also generate custom snowflake ids:
//! ```
//! let mut generator = Generator::new(0);
//! let id: UserId = generator.generate();
//! ```
//!
//! For more details on [`sync::Generator`] see the [`sync`] module.
//!
//! # Feature flags
//! `sync`: Enables the [`sync`] module.

#[cfg(feature = "sync")]
#[cfg_attr(docsrs, doc(cfg(feature = "sync")))]
pub mod sync;

use std::time::UNIX_EPOCH;

const BITMASK_INSTANCE: u64 = 0x3FF000;
const BITMASK_SEQUENCE: u64 = 0xFFF;

const INSTANCE_MAX: u16 = 2_u16.pow(10) - 1;

/// A type that can be used as a snowflake id.
pub trait Snowflake {
    /// Creates a new value from the snowflake parts.
    fn from_parts(timestamp: u64, instance: u64, sequence: u64) -> Self;

    /// Returns the timestamp component of the snowflake.
    fn timestamp(&self) -> u64;

    /// Returns the instance component of the snowflake.
    fn instance(&self) -> u64;

    /// Returns the sequence component of the snowflake.
    fn sequence(&self) -> u64;
}

impl Snowflake for u64 {
    fn from_parts(timestamp: u64, instance: u64, sequence: u64) -> Self {
        let timestamp = timestamp << 22;
        let instance = (instance << 12) & BITMASK_INSTANCE;
        timestamp + instance + sequence
    }

    #[inline]
    fn timestamp(&self) -> u64 {
        self >> 22
    }

    #[inline]
    fn instance(&self) -> u64 {
        (self & BITMASK_INSTANCE) >> 12
    }

    #[inline]
    fn sequence(&self) -> u64 {
        self & BITMASK_SEQUENCE
    }
}

impl Snowflake for i64 {
    fn from_parts(timestamp: u64, instance: u64, sequence: u64) -> Self {
        let timestamp = timestamp << 22;
        let instance = (instance << 12) & BITMASK_INSTANCE;
        timestamp as i64 + instance as i64 + sequence as i64
    }

    #[inline]
    fn timestamp(&self) -> u64 {
        *self as u64 >> 22
    }

    #[inline]
    fn instance(&self) -> u64 {
        (*self as u64 & BITMASK_INSTANCE) >> 12
    }

    #[inline]
    fn sequence(&self) -> u64 {
        *self as u64 & BITMASK_SEQUENCE
    }
}

/// A generator for unique snowflake ids.
#[derive(Clone, Debug)]
pub struct Generator {
    instance: u16,
    sequence: u16,
    timestamp: u64,
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

    /// Creates a new `Generator` using the given `instance` without checking if instance exceeds
    /// the maximum value (2^10 -1).
    ///
    /// Note: If `instance` exceeds the maximum instance value the `Generator` will create
    /// incorrect snowflakes.
    pub const fn new_unchecked(instance: u16) -> Self {
        Self {
            instance,
            sequence: 0,
            timestamp: 0,
        }
    }

    /// Generate a new unique snowflake id.
    pub fn generate<T>(&mut self) -> T
    where
        T: Snowflake,
    {
        self.sequence = (self.sequence + 1) % 4096;

        loop {
            let timestamp = UNIX_EPOCH.elapsed().unwrap().as_millis() as u64;

            if self.sequence != 0 || timestamp > self.timestamp {
                self.timestamp = timestamp;
                break;
            }

            std::hint::spin_loop();
        }

        let instance = self.instance as u64;
        let sequence = self.sequence as u64;

        T::from_parts(self.timestamp, instance, sequence)
    }
}

#[cfg(test)]
mod tests {
    use crate::Snowflake;

    use super::Generator;

    #[test]
    fn test_generate() {
        const INSTANCE: u64 = 0;

        let mut sequence = 1;
        let mut generator = Generator::new_unchecked(INSTANCE as u16);

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
        let mut generator = Generator::new_unchecked(0);
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
    fn test_snowflake_u64() {
        let id = 442252698964721669_u64;
        assert_eq!(id.timestamp(), 105441260091);
        assert_eq!(id.instance(), 0);
        assert_eq!(id.sequence(), 5);

        let id = 862026798833074178_u64;
        assert_eq!(id.timestamp(), 205523204525);
        assert_eq!(id.instance(), 256);
        assert_eq!(id.sequence(), 2);
    }

    #[test]
    fn test_snowflake_i64() {
        let id = 442252698964721669_u64;
        assert_eq!(id.timestamp(), 105441260091);
        assert_eq!(id.instance(), 0);
        assert_eq!(id.sequence(), 5);

        let id = 862026798833074178_u64;
        assert_eq!(id.timestamp(), 205523204525);
        assert_eq!(id.instance(), 256);
        assert_eq!(id.sequence(), 2);
    }
}
