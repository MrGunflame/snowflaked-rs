use std::time::{Duration, SystemTime};

pub(crate) trait Time: Copy {
    const DEFAULT: Self;

    fn elapsed(&self) -> Duration;
}

impl Time for SystemTime {
    const DEFAULT: Self = Self::UNIX_EPOCH;

    fn elapsed(&self) -> Duration {
        self.elapsed().expect("clock went backwards")
    }
}
