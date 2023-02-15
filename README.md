# Snowflaked

[![Crates.io](https://img.shields.io/crates/v/snowflaked)](https://crates.io/crates/snowflaked)
[![Docs.rs](https://img.shields.io/docsrs/snowflaked/latest)](https://docs.rs/snowflaked)

A crate for creating and working with snowflake ids.

## Usage

Add `snowflaked` to your `Cargo.toml`:

```toml
snowflaked = "1.0.0"
```

This crate provides APIs for generating new snowflake ids and defining custom snowflake types.

### Snowflake Generation

Use the `Generator` type to create new snowflake ids:

```rust
use snowflaked::Generator;

let mut generator = Generator::new(0);
let id: u64 = generator.generate();
```

Or use the thread-safe `sync::Generator` type (requires the optional `sync` feature):

```rust
use snowflaked::sync::Generator;

static GENERATOR: Generator = Generator::new(0);

fn generate_id() -> u64 {
    GENERATOR.generate()
}
```

### Using custom snowflake types

Custom snowflake types can be defined with the `Snowflake` trait. This trait is currently
implemented for `u64` and `i64` and can be used to define your custom types:

```rust
use snowflaked::Snowflake;

struct UserId(u64);

impl Snowflake for UserId {
    fn from_parts(timestamp: u64, instance: u64, sequence: u64) -> Self {
        Self(u64::from_parts(timestamp, instance, sequence))
    }

    fn timestamp(&self) -> u64 {
        self.0.timestamp()
    }

    fn instance(&self) -> u64 {
        self.0.instance()
    }

    fn sequence(&self) -> u64 {
        self.0.sequence()
    }
}
```

## License

Licensed under either 
- [MIT License](https://github.com/MrGunflame/snowflaked-rs/blob/master/LICENSE-MIT)
or
- [Apache License, Version 2.0](https://github.com/MrGunflame/snowflaked-rs/blob/master/LICENSE-APACHE)
at your option.
