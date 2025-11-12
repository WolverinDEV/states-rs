extern crate alloc;

mod state;
pub use state::{
    State,
    StateType,
};

mod registry;
pub use registry::StateRegistry;

mod slot;
