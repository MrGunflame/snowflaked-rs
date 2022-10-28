//! Thread-safe Snowflake Generator
//!
//! This module provides [`Generator`] which can safely be shared between threads. Its constructor
//! is also const allowing to use it in a `static` context.
//!
//! # Example
//! ```
//! use snowflaked::sync::Generator;
//!
//! static GENERATOR: Generator = Generator::new_unchecked(0);
//!
//! fn generate_id() -> u64 {
//!     GENERATOR.generate()
//! }
//! ```

use crate::{const_panic_new, Components, Snowflake, INSTANCE_MAX};

use std::mem::MaybeUninit;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::UNIX_EPOCH;

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
/// static GENERATOR: Generator = Generator::new_unchecked(0);
///
/// fn generate_id() -> u64 {
///     GENERATOR.generate()
/// }
/// ```
///
/// [`generate`]: Self::generate
/// [`Arc`]: std::sync::Arc
#[derive(Debug)]
pub struct Generator {
    components: AtomicU64,
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
            components: AtomicU64::new(Components::new(instance as u64).to_bits()),
        }
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
        let bits = self.components.load(Ordering::Relaxed);
        Components::from_bits(bits).instance() as u16
    }

    /// Generate a new unique snowflake id.
    pub fn generate<T>(&self) -> T
    where
        T: Snowflake,
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
                    let now = UNIX_EPOCH.elapsed().unwrap().as_millis() as u64;

                    if sequence != 4095 || now > components.timestamp() {
                        components.set_timestamp(now);
                        timestamp = now;
                        break;
                    }

                    std::hint::spin_loop();
                }

                let instance = components.instance();

                id.write(T::from_parts(timestamp, instance, sequence));

                Some(components.to_bits())
            });

        // SAFETY: The call to `fetch_update` only completes once the closure ran fully.
        // At this point `id` has been initialized from within the closure.
        unsafe { id.assume_init() }
    }
}

impl Clone for Generator {
    fn clone(&self) -> Self {
        let bits = self.components.load(Ordering::Relaxed);

        Self {
            components: AtomicU64::new(bits),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::sync::atomic::Ordering;
    use std::sync::mpsc;
    use std::thread;

    use super::Generator;
    use crate::{Components, Snowflake};

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

    #[test]
    fn test_generator_clone() {
        let orig = Generator::new_unchecked(0);

        let cloned = orig.clone();

        let orig_bits = Components::from_bits(orig.components.load(Ordering::Relaxed));
        let cloned_bits = Components::from_bits(cloned.components.load(Ordering::Relaxed));

        assert_eq!(orig_bits, cloned_bits);
    }
}
