use std::time::{Duration, SystemTime};

pub(crate) trait Time {
    fn elapsed(&self) -> Duration;
}

pub(crate) trait DefaultTime {
    const DEFAULT: Self;
}

impl Time for SystemTime {
    fn elapsed(&self) -> Duration {
        self.elapsed().expect("clock went backwards")
    }
}

impl DefaultTime for SystemTime {
    const DEFAULT: Self = Self::UNIX_EPOCH;
}
