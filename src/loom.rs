#[cfg(not(loom))]
pub(crate) use core::sync::atomic::{AtomicU64, Ordering};

#[cfg(loom)]
pub(crate) use loom::sync::atomic::{AtomicU64, Ordering};
