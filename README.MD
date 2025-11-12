# states-rs &emsp; [![Latest Version]][crates.io] [![License: GPL v3]](./LICENSE) [![GitHub build status]][actions]

[License: GPL v3]: https://img.shields.io/badge/License-GPLv3-blue.svg
[Latest Version]: https://img.shields.io/crates/v/states.svg
[crates.io]: https://crates.io/crates/states
[GitHub build status]: https://github.com/WolverinDEV/states-rs/workflows/Rust/badge.svg?branch=master
[actions]: https://github.com/WolverinDEV/states-rs/actions?query=workflow%3ARust

A lightweight, type-safe registry for managing cached and self-initializing states.

`states` lets you define reusable, parameterized objects that can be lazily created,
cached, and invalidated — ideal for dependency-aware systems or runtime caching.

## Example

```rust
use states::{State, StateRegistry, StateType};

struct Double(u64);

impl State for Double {
    type Error = std::convert::Infallible;
    type Parameter<'a> = u64;

    fn create(_: &StateRegistry, param: Self::Parameter<'_>) -> Result<Self, Self::Error> {
        Ok(Self(param * 2))
    }

    fn state_type(&self) -> StateType {
        StateType::Persistent
    }
}

fn main() {
    let registry = StateRegistry::new(0x10);
    let state = registry.resolve_with::<Double>(21).unwrap();
    assert_eq!(state.0, 42);
}
```

# Features
- Lazy creation and automatic caching
- Type-safe lookup by (TypeId, Parameter)
- Persistent and volatile caching policies
- Dependency-aware design

# Installation
```toml
[dependencies]
states = "0.1"
```