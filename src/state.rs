use core::hash::Hash;
use std::any::{
    Any,
    TypeId,
};

use crate::registry::StateRegistry;

pub type StateLookupKey = (TypeId, u64);

/// Defines the caching behavior of a [`State`] within the [`StateRegistry`].
///
/// Each state declares its persistence policy, determining how long it
/// remains valid and whether it can be automatically discarded or reused.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash)]
pub enum StateType {
    /// The state will be cached and never removed
    Persistent,

    /// The state will be removed as soon it get's invalidated.
    /// The update method will only be called once upon creation.
    Volatile,
}

/// Represents a typed, self-initializing, and potentially cached state.
///
/// Implementors define how to **create**, **parameterize**, and **cache**
/// instances of themselves inside a [`StateRegistry`]. Each state can define
/// its own initialization logic and error handling, as well as its caching
/// strategy via [`State::state_type`].
///
/// A state is uniquely identified by a combination of its type and its
/// [`Parameter`](Self::Parameter) value.
///
/// # Example
///
/// ```rust
/// # use states::{State, StateRegistry, StateType};
/// struct ExampleState(pub u64);
///
/// impl State for ExampleState {
///     type Error = std::convert::Infallible;
///     type Parameter<'a> = u64;
///
///     fn create(_registry: &StateRegistry, param: Self::Parameter<'_>) -> Result<Self, Self::Error> {
///         Ok(Self(param * 2))
///     }
///
///     fn state_type(&self) -> StateType {
///         StateType::Persistent
///     }
/// }
/// ```
pub trait State: Any + Sized + Send {
    /// The error type returned by [`create`](Self::create).
    type Error;

    /// The parameter type used to identify and construct this state.
    ///
    /// The parameter participates in lookup key computation via its
    /// [`Hash`] and [`PartialEq`] implementations.
    ///
    /// Each distinct parameter value represents a unique state instance.
    type Parameter<'a>: Hash + PartialEq;

    /// Creates a new instance of this state.
    ///
    /// Called automatically when the state is being created by the [`StateRegistry`].
    ///
    /// Implementations can perform arbitrary initialization logic here,
    /// such as computing derived data or resolving dependent states.
    ///
    /// # Errors
    ///
    /// Returns a [`Self::Error`] if the state could not be created successfully.
    fn create(registry: &StateRegistry, param: Self::Parameter<'_>) -> Result<Self, Self::Error>;

    /// Returns the caching policy of this state.
    ///
    /// By default, all states are considered [`StateType::Volatile`].
    ///
    /// Override this to return [`StateType::Persistent`] if the state
    /// should remain cached across invalidations.
    fn state_type(&self) -> StateType {
        StateType::Volatile
    }
}
