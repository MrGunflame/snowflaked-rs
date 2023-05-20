//! Thread-safe Snowflake Generator
//!
//! This module provides [`Generator`] which can safely be shared between threads. Its constructor
//! is also const allowing to use it in a `static` context.
//!
//! # Example
//! ```
//! use snowflaked::sync::Generator;
//!
//! static GENERATOR: Generator = Generator::new(0);
//!
//! fn generate_id() -> u64 {
//!     GENERATOR.generate()
//! }
//! ```

use std::mem::MaybeUninit;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::SystemTime;

use crate::builder::Builder;
use crate::time::Time;
use crate::{const_panic_new, Components, Snowflake, INSTANCE_MAX};

/// A generator for unique snowflake ids. Since [`generate`] accepts a `&self` reference this can
/// be used in a `static` context.
///
/// # Cloning
///
/// Cloning a `Generator` will create a second one with the same state as the original one. The
/// internal state is copied and not shared. If you need to share a single `Generator` you need to
/// manually wrap it in an [`Arc`] (or similar).
///
/// # Example
/// ```
/// use snowflaked::sync::Generator;
///
/// static GENERATOR: Generator = Generator::new(0);
///
/// fn generate_id() -> u64 {
///     GENERATOR.generate()
/// }
/// ```
///
/// [`generate`]: Self::generate
/// [`Arc`]: std::sync::Arc
pub struct Generator {
    internal: InternalGenerator<SystemTime>,
}

impl Generator {
    /// Creates a new `Generator` using the given `instance`.
    ///
    /// # Panics
    ///
    /// Panics if `instance` exceeds the maximum value (2^10 - 1).
    #[inline]
    pub const fn new(instance: u16) -> Self {
        match Self::new_checked(instance) {
            Some(this) => this,
            None => const_panic_new(),
        }
    }

    /// Creates a new `Generator` using the given `instance`. Returns `None` if the instance
    /// exceeds the maximum instance value (2^10 - 1).
    #[inline]
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
    #[inline]
    pub const fn new_unchecked(instance: u16) -> Self {
        Self {
            internal: InternalGenerator::new_unchecked(instance),
        }
    }

    /// Creates a new `Builder` used to configure a `Generator`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use snowflaked::sync::Generator;
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

    /// Returns the configured instance component of this `Generator`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use snowflaked::sync::Generator;
    /// #
    /// let mut generator = Generator::new(123);
    ///
    /// assert_eq!(generator.instance(), 123);
    /// ```
    #[inline]
    pub fn instance(&self) -> u16 {
        self.internal.instance()
    }

    /// Returns the configured epoch of this `Generator`. By default this is [`UNIX_EPOCH`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use snowflaked::sync::Generator;
    /// use std::time::UNIX_EPOCH;
    ///
    /// let generator = Generator::new(123);
    /// assert_eq!(generator.epoch(), UNIX_EPOCH);
    /// ```
    #[inline]
    pub fn epoch(&self) -> SystemTime {
        self.internal.epoch()
    }

    /// Generate a new unique snowflake id.
    pub fn generate<T>(&self) -> T
    where
        T: Snowflake,
    {
        self.internal.generate(std::hint::spin_loop)
    }
}

impl From<Builder> for Generator {
    fn from(builder: Builder) -> Self {
        let internal = InternalGenerator {
            components: AtomicU64::new(Components::new(builder.instance as u64).to_bits()),
            epoch: builder.epoch,
        };

        Self { internal }
    }
}

#[derive(Debug)]
struct InternalGenerator<T>
where
    T: Time,
{
    components: AtomicU64,
    epoch: T,
}

impl<T> InternalGenerator<T>
where
    T: Time,
{
    #[inline]
    const fn new_unchecked(instance: u16) -> Self {
        Self {
            components: AtomicU64::new(Components::new(instance as u64).to_bits()),
            epoch: T::DEFAULT,
        }
    }

    #[inline]
    fn instance(&self) -> u16 {
        let bits = self.components.load(Ordering::Relaxed);
        Components::from_bits(bits).instance() as u16
    }

    #[inline]
    fn epoch(&self) -> T {
        self.epoch
    }

    fn generate<S>(&self, tick_wait: fn()) -> S
    where
        S: Snowflake,
    {
        // Even thought we only assign this value once we need to assign this value to
        // something before passing it (reference) into the closure.
        // This value is safe to read after the closure completes.
        let mut id = MaybeUninit::uninit();

        let _ = self
            .components
            .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |bits| {
                let mut components = Components::from_bits(bits);

                let sequence = components.take_sequence();

                let timestamp;
                loop {
                    let now = self.epoch.elapsed().as_millis() as u64;

                    if sequence != 4095 || now > components.timestamp() {
                        components.set_timestamp(now);
                        timestamp = now;
                        break;
                    }

                    tick_wait();
                }

                let instance = components.instance();

                id.write(S::from_parts(timestamp, instance, sequence));

                Some(components.to_bits())
            });

        // SAFETY: The call to `fetch_update` only completes once the closure ran fully.
        // At this point `id` has been initialized from within the closure.
        unsafe { id.assume_init() }
    }
}

#[cfg(test)]
mod tests {
    use std::sync::mpsc;
    use std::thread;

    use super::Generator;
    use crate::Snowflake;

    #[test]
    fn test_generate() {
        const INSTANCE: u64 = 0;

        let mut sequence = 0;
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
    fn test_generate_threads() {
        const INSTANCE: u64 = 0;
        const THREADS: usize = 4;

        static GENERATOR: Generator = Generator::new_unchecked(INSTANCE as u16);

        let (tx, rx) = mpsc::sync_channel::<Vec<u64>>(THREADS);

        for _ in 0..THREADS {
            let tx = tx.clone();
            thread::spawn(move || {
                let mut ids = Vec::with_capacity(10_000);

                for _ in 0..10_000 {
                    ids.push(GENERATOR.generate());
                }

                tx.send(ids).unwrap();
            });
        }

        let mut ids = Vec::with_capacity(10_000 * THREADS);
        for _ in 0..THREADS {
            ids.extend(rx.recv().unwrap());
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
    fn test_generate_no_duplicates() {
        let generator = Generator::new_unchecked(0);
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

    // #[test]
    // fn test_generator_clone() {
    //     let orig = Generator::new_unchecked(0);

    //     let cloned = orig.clone();

    //     let orig_bits = Components::from_bits(orig.components.load(Ordering::Relaxed));
    //     let cloned_bits = Components::from_bits(cloned.components.load(Ordering::Relaxed));

    //     assert_eq!(orig_bits, cloned_bits);
    // }
}
