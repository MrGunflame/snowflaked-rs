//! A crate for working with snowflake ids.
//!
//! Most notably this provides [`Snowflake`] for working with custom snowflake ids and
//! [`Generator`] creating new snowflake ids.
//!
//! # Snowflake structure
//!
//! A snowflake id is a 64-bit integer generated using the current timestamp in milliseconds, a
//! constant instance and a sequence number.
//!
//! ```text
//! 0               1               2                 3               4                 5               6               7
//! 0 1 2 3 4 5 6 7 0 1 2 3 4 5 6 7 0 1 2 3 4 5 6 7 8 0 1 2 3 4 5 6 7 0 1 2 3 4 5 6 7 8 0 1 2 3 4 5 6 7 0 1 2 3 4 5 6 7 0 1 2 3 4 5 6 7
//! +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
//! |                                       Timestamp                                       |     Instance      |       Sequence      |
//! +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
//! ```
//!
//! - The [`Snowflake`] implementation for `u64` uses 42 bits for the timestamp, 10 bits for the
//!   instance and 12 bits for the sequence.
//! - The [`Snowflake`] implementation for `i64` uses 41 bits for the timestamp, 10 bits for the
//!   instance and 12 bits for the sequence.
//!
//! ## Timestamp overflow
//!
//! Since the timestamp range is limited it is possible for the timestamp to overflow and wrap
//! around after a specific date. For the by-default configured UNIX epoch these dates are:
//! - For `i64`: Sep 07 2039 15:47:35 (`2039-09-07T15:47:35Z`)
//! - For `u64`: May 15 2109 07:35:11 (`2109-05-15T07:35:11Z`)
//!
//! If overflowing after these dates is not acceptable for you [`Builder::epoch`] allows
//! configuring a custom epoch.
//!
//! # Custom snowflake ids
//!
//! Custom snowflake ids can be created with the [`Snowflake`] trait.
//!
//! ## Example
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
//! ## Example
//! ```
//! use snowflaked::Generator;
//!
//! let mut generator = Generator::new(0);
//! let id: u64 = generator.generate();
//! ```
//!
//! [`Generator::generate`] can also generate custom snowflake ids:
//! ```
//! # use snowflaked::Snowflake;
//! #
//! # pub struct UserId(u64);
//! #
//! # impl Snowflake for UserId {
//! #    fn from_parts(timestamp: u64, instance: u64, sequence: u64) -> Self {
//! #       Self(u64::from_parts(timestamp, instance, sequence))
//! #    }
//! #
//! #    fn timestamp(&self) -> u64 {
//! #        self.0.timestamp()
//! #    }
//! #
//! #    fn instance(&self) -> u64 {
//! #        self.0.instance()
//! #    }
//! #
//! #    fn sequence(&self) -> u64 {
//! #        self.0.sequence()
//! #    }
//! # }
//!
//! use snowflaked::Generator;
//!
//! let mut generator = Generator::new(0);
//! let id: UserId = generator.generate();
//! ```
//!
//! For more details on [`sync::Generator`] see the [`sync`] module.
//!
//! # Feature flags
//! `sync`: Enables the [`sync`] module.
#![cfg_attr(docsrs, feature(doc_cfg))]

mod builder;
mod loom;
mod time;

#[cfg(feature = "sync")]
#[cfg_attr(docsrs, doc(cfg(feature = "sync")))]
pub mod sync;

pub use builder::Builder;

use std::time::{SystemTime, UNIX_EPOCH};

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
        timestamp | instance | sequence
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
        // Don't set the sign bit.
        let timestamp = (timestamp << 22) & (i64::MAX as u64);
        let instance = (instance << 12) & BITMASK_INSTANCE;
        (timestamp | instance | sequence) as i64
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

/// A generator for new unique [`Snowflake`] ids.
///
/// # Examples
///
/// ```
/// # use snowflaked::Generator;
/// #
/// let mut generator = Generator::new(0);
///
/// let id: u64 = generator.generate();
/// ```
#[derive(Debug)]
pub struct Generator {
    components: Components,
    epoch: SystemTime,
}

impl Generator {
    /// Creates a new `Generator` using the given `instance`.
    ///
    /// # Panics
    ///
    /// Panics if `instance` exceeds the maximum value (2^10 - 1).
    ///
    /// # Examples
    ///
    /// ```
    /// # use snowflaked::Generator;
    /// #
    /// let mut generator = Generator::new(123);
    ///
    /// assert_eq!(generator.instance(), 123);
    /// ```
    ///
    /// Providing an invalid `instance` will panic.
    ///
    /// ```should_panic
    /// # use snowflaked::Generator;
    /// #
    /// let mut generator = Generator::new(10_000);
    /// ```
    #[inline]
    pub const fn new(instance: u16) -> Self {
        match Self::new_checked(instance) {
            Some(this) => this,
            None => const_panic_new(),
        }
    }

    /// Creates a new `Generator` using the given `instance`. Returns `None` if the instance
    /// exceeds the maximum instance value (2^10 - 1).
    ///
    /// # Examples
    ///
    /// ```
    /// # use snowflaked::Generator;
    /// #
    /// let mut generator = Generator::new_checked(123).unwrap();
    ///
    /// assert_eq!(generator.instance(), 123);
    /// ```
    #[inline]
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
    ///
    /// # Examples
    ///
    /// ```
    /// # use snowflaked::Generator;
    /// #
    /// let mut generator = Generator::new_unchecked(123);
    ///
    /// assert_eq!(generator.instance(), 123);
    /// ```
    #[inline]
    pub const fn new_unchecked(instance: u16) -> Self {
        Self {
            components: Components::new(instance as u64),
            epoch: UNIX_EPOCH,
        }
    }

    /// Creates a new `Builder` used to configure a `Generator`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use snowflaked::Generator;
    /// use std::time::SystemTime;
    ///
    /// let epoch = SystemTime::now();
    /// let generator: Generator = Generator::builder().instance(123).epoch(epoch).build();
    ///
    /// assert_eq!(generator.instance(), 123);
    /// assert_eq!(generator.epoch(), epoch);
    /// ```
    #[inline]
    pub const fn builder() -> Builder {
        Builder::new()
    }

    /// Returns the configured instace component of this `Generator`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use snowflaked::Generator;
    /// #
    /// let mut generator = Generator::new(123);
    ///
    /// assert_eq!(generator.instance(), 123);
    /// ```
    #[inline]
    pub fn instance(&self) -> u16 {
        self.components.instance() as u16
    }

    /// Returns the configured epoch of this `Generator`. By default this is [`UNIX_EPOCH`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use snowflaked::Generator;
    /// use std::time::UNIX_EPOCH;
    ///
    /// let generator = Generator::new(123);
    /// assert_eq!(generator.epoch(), UNIX_EPOCH);
    /// ```
    #[inline]
    pub fn epoch(&self) -> SystemTime {
        self.epoch
    }

    /// Generate a new unique snowflake id.
    ///
    /// # Examples
    ///
    /// ```
    /// # use snowflaked::Generator;
    /// #
    /// let mut generator = Generator::new(0);
    ///
    /// let id1: u64 = generator.generate();
    /// let id2: i64 = generator.generate();
    /// ```
    pub fn generate<T>(&mut self) -> T
    where
        T: Snowflake,
    {
        use std::cmp::Ordering;

        let mut now = self.epoch.elapsed().unwrap().as_millis() as u64;
        let instance = self.components.instance();
        match now.cmp(&self.components.timestamp()) {
            Ordering::Less => {
                panic!("Clock has moved backwards! This is not supported.");
            }
            Ordering::Greater => {
                self.components.reset_sequence();
                self.components.set_timestamp(now);
                T::from_parts(now, instance, 0)
            }
            Ordering::Equal => {
                let sequence = self.components.take_sequence();
                if sequence == 0 {
                    now = self.wait_until_next_millisecond(now);
                }
                self.components.set_timestamp(now);
                T::from_parts(now, instance, sequence)
            }
        }
    }

    fn wait_until_next_millisecond(&mut self, last_millisecond: u64) -> u64 {
        loop {
            let now = self.epoch.elapsed().unwrap().as_millis() as u64;
            if now > last_millisecond {
                return now;
            }
            std::hint::spin_loop();
        }
    }
}

impl From<Builder> for Generator {
    fn from(builder: Builder) -> Self {
        Self {
            components: Components::new(builder.instance as u64),
            epoch: builder.epoch,
        }
    }
}

/// A single `u64` representing the complete current state of a generator.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
#[repr(transparent)]
pub(crate) struct Components(u64);

impl Components {
    #[inline]
    pub(crate) const fn new(instance: u64) -> Self {
        // Fill in the given instance, and set the sequence at '1'
        Self((instance << 12) & BITMASK_INSTANCE | 1)
    }

    #[inline]
    pub(crate) fn sequence(&self) -> u64 {
        self.0 & BITMASK_SEQUENCE
    }

    #[inline]
    pub(crate) fn instance(&self) -> u64 {
        (self.0 & BITMASK_INSTANCE) >> 12
    }

    #[inline]
    pub(crate) fn timestamp(&self) -> u64 {
        self.0 >> 22
    }

    pub(crate) fn set_sequence(&mut self, seq: u64) {
        let timestamp = self.timestamp() << 22;
        let instance = (self.instance() << 12) & BITMASK_INSTANCE;
        *self = Self(timestamp + instance + seq)
    }

    pub(crate) fn reset_sequence(&mut self) {
        self.set_sequence(1)
    }

    pub(crate) fn set_timestamp(&mut self, ts: u64) {
        let timestamp = ts << 22;
        let instance = (self.instance() << 12) & BITMASK_INSTANCE;
        *self = Self(timestamp + instance + self.sequence())
    }

    #[inline]
    pub(crate) fn take_sequence(&mut self) -> u64 {
        match self.sequence() {
            4095 => {
                self.set_sequence(0);
                4095
            }
            n => {
                self.set_sequence(n + 1);
                n
            }
        }
    }

    #[inline]
    pub(crate) const fn from_bits(bits: u64) -> Self {
        Self(bits)
    }

    #[inline]
    pub(crate) const fn to_bits(self) -> u64 {
        self.0
    }
}

/// Emits a panic with the appropriate message for providing an invalid instance id to
/// a generator.
#[inline(never)]
#[cold]
pub(crate) const fn const_panic_new() -> ! {
    panic!("invalid instance provided for snowflake generator");
}

#[cfg(all(test, not(loom)))]
mod tests {
    use std::time::UNIX_EPOCH;

    use super::Generator;
    use crate::{Components, Snowflake};

    #[test]
    fn test_components() {
        let mut components = Components::new(0);
        assert_eq!(components.sequence(), 1);
        assert_eq!(components.timestamp(), 0);

        components.set_sequence(1024);
        assert_eq!(components.sequence(), 1024);
        assert_eq!(components.timestamp(), 0);

        components.set_timestamp(1024);
        assert_eq!(components.sequence(), 1024);
        assert_eq!(components.timestamp(), 1024);

        let now = UNIX_EPOCH.elapsed().unwrap().as_millis() as u64;
        components.set_timestamp(now);
        assert_eq!(components.sequence(), 1024);
        assert_eq!(components.timestamp(), now);
    }

    #[test]
    fn test_generate_ordered() {
        const INSTANCE: u64 = 0;

        let mut last_id = None;
        let mut generator = Generator::new_unchecked(INSTANCE as u16);

        for _ in 0..10_000 {
            let id: u64 = generator.generate();
            assert_eq!(id.instance(), INSTANCE);
            assert!(
                last_id < Some(id),
                "expected {:?} to be less than {:?}",
                last_id,
                Some(id)
            );
            last_id = Some(id);
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
                if index != index2 && id == id2 {
                    panic!(
                        "Found duplicate id {} (SEQ {}, INS {}, TS {}) at index {} and {}",
                        id,
                        id.sequence(),
                        id.instance(),
                        id.timestamp(),
                        index,
                        index2
                    );
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
        let id = 442252698964721669_i64;
        assert_eq!(id.timestamp(), 105441260091);
        assert_eq!(id.instance(), 0);
        assert_eq!(id.sequence(), 5);

        let id = 862026798833074178_i64;
        assert_eq!(id.timestamp(), 205523204525);
        assert_eq!(id.instance(), 256);
        assert_eq!(id.sequence(), 2);
    }

    #[test]
    fn i64_no_negative() {
        let timestamp = 2297684976571;
        let instance = 0;
        let sequence = 0;

        let id = i64::from_parts(timestamp, instance, sequence);
        assert!(id >= 0);
    }

    #[test]
    fn i64_reflexive() {
        let timestamp = 1684917000190;
        let instance = 0;
        let sequence = 2056;

        let id = i64::from_parts(timestamp, instance, sequence);

        assert_eq!(id.timestamp(), timestamp);
        assert_eq!(id.instance(), instance);
        assert_eq!(id.sequence(), sequence);
    }

    #[test]
    fn u64_reflexive() {
        let timestamp = 1684917075097;
        let instance = 0;
        let sequence = 1086;

        let id = u64::from_parts(timestamp, instance, sequence);

        assert_eq!(id.timestamp(), timestamp);
        assert_eq!(id.instance(), instance);
        assert_eq!(id.sequence(), sequence);
    }

    #[test]
    fn u64_i64_equivalent() {
        let timestamp = 1684917177537;
        let instance = 0;
        let sequence = 3060;

        let id0 = u64::from_parts(timestamp, instance, sequence);
        let id1 = i64::from_parts(timestamp, instance, sequence);

        assert_eq!(id0.timestamp(), id1.timestamp());
        assert_eq!(id0.instance(), id1.instance());
        assert_eq!(id0.sequence(), id1.sequence());
    }
}
