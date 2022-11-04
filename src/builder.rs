use std::time::{SystemTime, UNIX_EPOCH};

use crate::{const_panic_new, INSTANCE_MAX};

/// A builder for a snowflake Generator. This builder can be used for both [`Generator`] and
/// [`sync::Generator`].
///
/// [`Generator`]: crate::Generator
/// [`sync::Generator`]: crate::sync::Generator
#[derive(Copy, Clone, Debug)]
pub struct Builder {
    pub(crate) instance: u16,
    pub(crate) epoch: SystemTime,
}

impl Builder {
    /// Creates a new `Builder` with the instance set to `0` and epoch set to [`UNIX_EPOCH`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::time::UNIX_EPOCH;
    /// # use snowflaked::{Builder, Generator};
    /// #
    /// let generator: Generator = Builder::new().build();
    ///
    /// assert_eq!(generator.instance(), 0);
    /// assert_eq!(generator.epoch(), UNIX_EPOCH);
    /// ```
    #[inline]
    pub const fn new() -> Self {
        Self {
            instance: 0,
            epoch: UNIX_EPOCH,
        }
    }

    /// Sets the `instance` value of the `Builder`.
    ///
    /// # Panics
    ///
    /// Panics if the provided `instance` exceeds the maximum value (2^10 -1).
    ///
    /// # Examples
    ///
    /// ```
    /// # use snowflaked::{Builder, Generator};
    /// #
    /// let generator: Generator = Builder::new().instance(400).build();
    ///
    /// assert_eq!(generator.instance(), 400);
    /// ```
    ///
    /// Providing an invalid `instance` panics:
    ///
    /// ```should_panic
    /// # use snowflaked::{Builder, Generator};
    /// #
    /// let generator: Generator = Builder::new().instance(5000).build();
    /// ```
    #[inline]
    pub const fn instance(self, instance: u16) -> Self {
        match self.instance_checked(instance) {
            Some(this) => this,
            None => const_panic_new(),
        }
    }

    /// Sets the `instance` value of the `Builder`. Returns `None` if the provided `instance`
    /// exceeds the maximum value (2^10 -1).
    ///
    /// # Examples
    ///
    /// ```
    /// # use snowflaked::{Builder, Generator};
    /// #
    /// let builder = Builder::new().instance_checked(400);
    /// assert!(builder.is_some());
    /// ```
    ///
    /// Providing an invalid `instance` returns `None`:
    ///
    /// ```
    /// # use snowflaked::{Builder, Generator};
    /// #
    /// let builder = Builder::new().instance_checked(5000);
    /// assert!(builder.is_none());
    /// ```
    #[inline]
    pub const fn instance_checked(mut self, instance: u16) -> Option<Self> {
        if instance > INSTANCE_MAX {
            None
        } else {
            self.instance = instance;
            Some(self)
        }
    }

    /// Sets the `instance` value of the `Builder` without validating whether `instance` exceeds
    /// the maximum value (2^10 - 1).
    ///
    /// # Examples
    ///
    /// ```
    /// # use snowflaked::{Builder, Generator};
    /// #
    /// let generator: Generator = Builder::new().instance_unchecked(400).build();
    ///
    /// assert_eq!(generator.instance(), 400);
    /// ```
    #[inline]
    pub const fn instance_unchecked(mut self, instance: u16) -> Self {
        self.instance = instance;
        self
    }

    #[inline]
    pub const fn epoch(mut self, epoch: SystemTime) -> Self {
        self.epoch = epoch;
        self
    }

    /// Consumes this `Builder`, returning the constructed generator. This function works with both
    /// [`Generator`] and [`sync::Generator`].
    ///
    /// # Examples
    ///
    /// ```
    /// use snowflaked::{Builder, Generator};
    ///
    /// let mut generator = Builder::new().build::<Generator>();
    ///
    /// let id: u64 = generator.generate();
    /// ```
    ///
    /// A [`sync::Generator`] can be constructed in the same way:
    ///
    /// ```
    /// use snowflaked::Builder;
    /// use snowflaked::sync::Generator;
    ///
    /// let generator = Builder::new().build::<Generator>();
    ///
    /// let id: u64 = generator.generate();
    /// ```
    ///
    /// [`Generator`]: crate::Generator
    /// [`sync::Generator`]: crate::sync::Generator
    #[inline]
    pub fn build<T>(self) -> T
    where
        T: From<Self>,
    {
        T::from(self)
    }
}
