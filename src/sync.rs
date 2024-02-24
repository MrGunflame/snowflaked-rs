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

use std::time::SystemTime;

use crate::builder::Builder;
use crate::loom::{AtomicU64, Ordering};
use crate::time::{DefaultTime, Time};
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
#[derive(Debug)]
pub struct Generator {
    internal: InternalGenerator<SystemTime>,
}

impl Generator {
    /// Creates a new `Generator` using the given `instance`.
    ///
    /// # Panics
    ///
    /// Panics if `instance` exceeds the maximum value (2^10 - 1).
    #[cfg(not(loom))]
    #[inline]
    pub const fn new(instance: u16) -> Self {
        match Self::new_checked(instance) {
            Some(this) => this,
            None => const_panic_new(),
        }
    }

    /// Creates a new `Generator` using the given `instance`. Returns `None` if the instance
    /// exceeds the maximum instance value (2^10 - 1).
    #[cfg(not(loom))]
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
    #[cfg(not(loom))]
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
    ///
    /// [`UNIX_EPOCH`]: std::time::UNIX_EPOCH
    #[inline]
    pub fn epoch(&self) -> SystemTime {
        self.internal.epoch()
    }

    /// Generate a new unique snowflake id.
    pub fn generate<T>(&self) -> T
    where
        T: Snowflake,
    {
        self.internal.generate(&std::hint::spin_loop)
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
    #[cfg(not(loom))]
    #[inline]
    const fn new_unchecked(instance: u16) -> Self
    where
        T: DefaultTime,
    {
        Self {
            components: AtomicU64::new(Components::new(instance as u64).to_bits()),
            epoch: T::DEFAULT,
        }
    }

    // AtomicU64 is not const, we have to choose a different code path
    // than the regular `new_unchecked`.
    #[cfg(loom)]
    #[inline]
    fn new_unchecked(instance: u16) -> Self
    where
        T: DefaultTime,
    {
        Self {
            components: AtomicU64::new(Components::new(instance as u64).to_bits()),
            epoch: T::DEFAULT,
        }
    }

    #[cfg(loom)]
    #[inline]
    fn new_unchecked_with_epoch(instance: u16, epoch: T) -> Self {
        Self {
            components: AtomicU64::new(Components::new(instance as u64).to_bits()),
            epoch,
        }
    }

    #[inline]
    fn instance(&self) -> u16 {
        let bits = self.components.load(Ordering::Relaxed);
        Components::from_bits(bits).instance() as u16
    }

    #[inline]
    fn epoch(&self) -> T
    where
        T: Copy,
    {
        self.epoch
    }

    fn generate<S, F>(&self, tick_wait: &F) -> S
    where
        S: Snowflake,
        F: Fn(),
    {
        use std::cmp;

        // Since `fetch_update` doesn't return a result,
        // we store the result in this mutable variable.
        // Note that using MaybeUninit is not necessary
        // as the compiler is smart enough to elide the Option for us.
        let mut id = None;

        let _ = self
            .components
            .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |bits| {
                let mut components = Components::from_bits(bits);
                let mut now = self.epoch.elapsed().as_millis() as u64;
                let instance = components.instance();
                match now.cmp(&components.timestamp()) {
                    cmp::Ordering::Less => {
                        panic!("Clock has moved backwards! This is not supported");
                    }
                    cmp::Ordering::Greater => {
                        components.reset_sequence();
                        components.set_timestamp(now);
                        id = Some(S::from_parts(now, instance, 0));
                        Some(components.to_bits())
                    }
                    cmp::Ordering::Equal => {
                        let sequence = components.take_sequence();
                        if sequence == 0 {
                            now = Self::wait_until_next_millisecond(&self.epoch, now, tick_wait);
                        }
                        components.set_timestamp(now);
                        id = Some(S::from_parts(now, instance, sequence));
                        Some(components.to_bits())
                    }
                }
            });
        id.expect("ID should have been set within the fetch_update closure.")
    }

    fn wait_until_next_millisecond<F>(epoch: &T, last_millisecond: u64, tick_wait: F) -> u64
    where
        F: Fn(),
    {
        loop {
            let now = epoch.elapsed().as_millis() as u64;
            if now > last_millisecond {
                return now;
            }
            tick_wait();
        }
    }
}

#[cfg(all(test, not(loom)))]
mod tests {
    use std::sync::mpsc;
    use std::thread;

    use super::Generator;
    use crate::Snowflake;

    #[test]
    fn test_generate() {
        const INSTANCE: u64 = 0;

        let mut last_id = None;
        let generator = Generator::new_unchecked(INSTANCE as u16);

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

#[cfg(all(test, loom))]
mod loom_tests {
    use std::sync::{mpsc, Arc, Mutex};
    use std::time::Duration;

    use loom::thread;

    use super::InternalGenerator;
    use crate::loom::Ordering;
    use crate::time::{DefaultTime, Time};
    use crate::Components;

    #[derive(Copy, Clone, Debug)]
    pub struct TestTime(u64);

    impl Time for TestTime {
        fn elapsed(&self) -> Duration {
            Duration::from_millis(self.0)
        }
    }

    impl DefaultTime for TestTime {
        const DEFAULT: Self = Self(0);
    }

    fn panic_on_wait() {
        panic!("unexpected wait");
    }

    const THREADS: usize = 2;

    #[test]
    fn no_duplicates_no_wrap() {
        loom::model(|| {
            let generator = Arc::new(InternalGenerator::<TestTime>::new_unchecked(0));
            let (tx, rx) = mpsc::channel();

            let threads: Vec<_> =
                (0..THREADS)
                    .map(|_| {
                        let generator = generator.clone();
                        let tx = tx.clone();

                        thread::spawn(move || {
                            let id: u64 = generator.generate(panic_on_wait);
                            tx.send(id).unwrap();
                        })
                    })
                    .collect();

            for th in threads {
                th.join().unwrap();
            }

            let id1 = rx.recv().unwrap();
            let id2 = rx.recv().unwrap();
            assert_ne!(id1, id2);
        });
    }

    #[test]
    fn no_duplicates_wrap() {
        static DEFAULT_TIME: Mutex<u64> = Mutex::new(0);

        // FIXME: Using raw pointers here is not optimal, but
        // required to get DEFAULT working. Maybe
        #[derive(Clone, Debug)]
        struct TestTimeWrap(Arc<Mutex<u64>>);

        impl Time for TestTimeWrap {
            fn elapsed(&self) -> Duration {
                let ms = self.0.lock().unwrap();
                Duration::from_millis(*ms)
            }
        }

        loom::model(|| {
            let ticked = Arc::new(Mutex::new(false));
            let time = Arc::new(Mutex::new(0));

            let mut generator =
                InternalGenerator::new_unchecked_with_epoch(0, TestTimeWrap(time.clone()));

            // Move the generator into a wrapping state.
            generator.components.with_mut(|bits| {
                let mut components = Components::from_bits(*bits);
                components.set_sequence(4095);
                *bits = components.to_bits();
            });

            let generator = Arc::new(generator);
            let (tx, rx) = mpsc::channel();

            let threads: Vec<_> = (0..THREADS)
                .map(|_| {
                    let ticked = ticked.clone();
                    let time = time.clone();

                    let generator = generator.clone();
                    let tx = tx.clone();

                    thread::spawn(move || {
                        let id: u64 = generator.generate(move || {
                            let mut ticked = ticked.lock().unwrap();

                            if !*ticked {
                                *ticked = true;

                                let mut ms = time.lock().unwrap();
                                *ms += 1;
                            }
                        });

                        tx.send(id).unwrap();
                    })
                })
                .collect();

            for th in threads {
                th.join().unwrap();
            }

            let id1 = rx.recv().unwrap();
            let id2 = rx.recv().unwrap();
            assert_ne!(id1, id2);
        });
    }
}
