use alloc::{
    boxed::Box,
    vec::Vec,
};
use core::{
    any::{
        Any,
        TypeId,
    },
    cell::{
        Ref,
        RefCell,
        RefMut,
    },
    hash::BuildHasher,
};

use hashbrown::DefaultHashBuilder;

use crate::{
    slot::{
        SlotAllocator,
        SlotState,
    },
    state::StateLookupKey,
    State,
    StateType,
};

#[derive(Default)]
struct StateValue {
    inner: RefCell<Option<Box<dyn Any>>>,
}

impl StateValue {
    fn initialize<S: State>(
        &self,
        registry: &StateRegistry,
        parameter: S::Parameter<'_>,
    ) -> Result<StateType, S::Error> {
        let value = Box::new(S::create(registry, parameter)?);
        let state_type = value.state_type();

        *self
            .inner
            .try_borrow_mut()
            .expect("internal error: slot should not have any references") = Some(value);

        Ok(state_type)
    }

    fn try_clear(&self) -> bool {
        let Ok(mut inner) = self.inner.try_borrow_mut() else {
            return false;
        };

        *inner = None;
        true
    }

    pub fn state_ref<S: State>(&self) -> Ref<'_, S> {
        let Ok(inner) = self.inner.try_borrow() else {
            panic!("state already borrowed as muteable");
        };

        Ref::map(inner, |inner| {
            inner
                .as_ref()
                .expect("a state to be present")
                .downcast_ref::<S>()
                .expect("state to be of type S")
        })
    }

    pub fn state_mut<S: State>(&self) -> RefMut<'_, S> {
        let Ok(inner) = self.inner.try_borrow_mut() else {
            panic!("state already borrowed as reference");
        };

        RefMut::map(inner, |inner| {
            inner
                .as_mut()
                .expect("a state to be present")
                .downcast_mut::<S>()
                .expect("state to be of type S")
        })
    }
}

/// A registry that manages and caches typed `State` instances.
///
/// Each state is uniquely identified by a combination of its type and a hash
/// derived from its parameter. The registry manages allocation and lifetime
/// of these states through an internal [`SlotAllocator`] and enforces
/// controlled access (borrowing, initialization, mutation) to maintain
/// consistency across concurrent or recursive operations.
pub struct StateRegistry {
    /// Allocates and manages slots within the registry.
    ///
    /// Each slot is identified by a lookup key (type + parameter hash) and may
    /// contain one state instance. The allocator tracks slot ownership and
    /// availability, ensuring that states are not mutated out of order.
    ///
    /// **Note:** You must hold a lock on this allocator (either by reference or
    /// mutable borrow) when accessing or mutating state values. Even if this is not
    /// strictly required now, future `Sync` implementations rely on this
    /// guarantee to preserve ordering and prevent data races.
    allocator: RefCell<SlotAllocator>,

    /// Holds all state values. Assignments are managed by the allocator.
    values: Box<[StateValue]>,

    hash: DefaultHashBuilder,
}

impl StateRegistry {
    /// Creates a new [`StateRegistry`] with a fixed capacity.
    ///
    /// The capacity defines how many individual states can be stored at once.
    pub fn new(capacity: usize) -> Self {
        let mut states = Vec::with_capacity(capacity);
        states.resize_with(capacity, Default::default);

        Self {
            allocator: RefCell::new(SlotAllocator::new(capacity)),
            values: states.into_boxed_slice(),
            hash: DefaultHashBuilder::default(),
        }
    }

    /// Computes the lookup key for a given state type and parameter.
    ///
    /// The lookup key is composed of the state’s [`TypeId`] and a hash
    /// of its parameter, and is used to uniquely identify cached state entries.
    fn compute_state_lookup_key<T: State>(&self, params: &T::Parameter<'_>) -> StateLookupKey {
        (TypeId::of::<T>(), self.hash.hash_one(params))
    }

    /// Drops all volatile states currently held in the registry.
    ///
    /// Volatile states are those marked with [`StateType::Volatile`]; they are
    /// temporary by design and can be recreated when needed.
    ///
    /// # Note
    ///
    /// This method does **not** drop statis with existing references
    /// to volatile values. If a reference is currently being held to a volatile state,
    /// that reference and hence the state remains valid until the next `drop_volatile` call.
    pub fn drop_volatile(&self) {
        let mut allocator = self.allocator.borrow_mut();

        for slot_index in 0..self.values.len() {
            let SlotState::Occupied {
                state_type,
                lookup_key,
            } = allocator.get_slot(slot_index)
            else {
                continue;
            };

            if *state_type != StateType::Volatile {
                continue;
            }

            if !self.values[slot_index].try_clear() {
                /* still some reference were held */
                continue;
            }

            let lookup_key = *lookup_key;
            allocator.free_slot(&lookup_key);
        }
    }

    /// Sets or replaces the value of a given state.
    ///
    /// The provided value will overwrite any existing entry occupying the same
    /// slot (based on the computed lookup key).
    ///
    /// # Panics
    ///
    /// - If the state is currently borrowed (immutably or mutably).
    /// - If the state is being initialized.
    ///
    /// This ensures no concurrent mutation or initialization conflicts occur.
    pub fn set_with<S: State>(&self, parameter: S::Parameter<'_>, value: impl Into<Box<S>>) {
        let value = value.into();
        let state_type = value.state_type();

        let lookup_key = self.compute_state_lookup_key::<S>(&parameter);

        let mut allocator = self.allocator.borrow_mut();
        let (slot_index, slot_state) = allocator.allocate_slot(lookup_key);

        let Ok(mut slot_value) = self.values[slot_index].inner.try_borrow_mut() else {
            panic!("can not set state value while still having references to that value");
        };

        match slot_state {
            SlotState::Empty | SlotState::Occupied { .. } => {
                *slot_state = SlotState::Occupied {
                    state_type,
                    lookup_key,
                }
            }
            SlotState::Initializing => {
                panic!("can not set state value while initializing that value")
            }
        }

        *slot_value = Some(value);
    }

    /// Returns an immutable reference to the specified state, if it exists.
    ///
    /// # Panics
    ///
    /// - If the state is currently initializing.
    /// - If a mutable reference to the state is already held.
    pub fn get_with<S: State>(&self, parameter: S::Parameter<'_>) -> Option<Ref<'_, S>> {
        let lookup_key = self.compute_state_lookup_key::<S>(&parameter);

        let allocator = self.allocator.borrow_mut();
        let (slot_index, slot_state) = allocator.lookup_slot(&lookup_key)?;
        match slot_state {
            SlotState::Empty => None,
            SlotState::Initializing => panic!("trying to access a state which is initializing"),
            SlotState::Occupied { .. } => Some(self.values[slot_index].state_ref::<S>()),
        }
    }

    /// Returns a mutable reference to the specified state, if it exists.
    ///
    /// # Panics
    ///
    /// - If the state is currently initializing.
    /// - If any (mutable or immutable) references to the same state are held.
    pub fn get_with_mut<S: State>(&self, parameter: S::Parameter<'_>) -> Option<RefMut<'_, S>> {
        let lookup_key = self.compute_state_lookup_key::<S>(&parameter);
        let allocator = self.allocator.borrow_mut();
        let (slot_index, slot_state) = allocator.lookup_slot(&lookup_key)?;
        match slot_state {
            SlotState::Empty => None,
            SlotState::Initializing => panic!("trying to access a state which is initializing"),
            SlotState::Occupied { .. } => Some(self.values[slot_index].state_mut::<S>()),
        }
    }

    fn do_resolve<'a, S: State, F: FnOnce(&'a StateValue) -> R, R>(
        &'a self,
        parameter: S::Parameter<'_>,
        slot_callback: F,
    ) -> Result<R, S::Error> {
        let lookup_key = self.compute_state_lookup_key::<S>(&parameter);

        let mut allocator = self.allocator.borrow_mut();
        let (slot_index, slot_state) = allocator.allocate_slot(lookup_key);

        match slot_state {
            SlotState::Empty => {
                /* mark as initialisation and drop allocator lock while initializing */
                *slot_state = SlotState::Initializing;
                drop(allocator);

                match self.values[slot_index].initialize::<S>(self, parameter) {
                    Ok(state_type) => {
                        let mut allocator = self.allocator.borrow_mut();
                        allocator.promote_slot(lookup_key, state_type);

                        Ok(slot_callback(&self.values[slot_index]))
                    }
                    Err(error) => {
                        let mut allocator = self.allocator.borrow_mut();
                        allocator.free_slot(&lookup_key);

                        Err(error)
                    }
                }
            }
            SlotState::Initializing => panic!("trying to access a state which is initializing"),
            SlotState::Occupied { .. } => Ok(slot_callback(&self.values[slot_index])),
        }
    }

    /// Resolves (creates or retrieves) an immutable reference to a state.
    ///
    /// If the state does not exist, it will be initialized in place.
    ///
    /// # Panics
    ///
    /// - If the state is currently being initialized.
    /// - If there are outstanding references that would violate borrow rules.
    ///
    /// # Errors
    ///
    /// Returns the states [`S::Error`] if the state’s initialization fails.
    ///
    /// # Warning
    ///
    /// Be cautious of circular dependencies — for example:
    /// `StateA` resolving `StateB` while `StateB` also attempts to resolve `StateA`.
    pub fn resolve_with<S: State>(
        &self,
        parameter: S::Parameter<'_>,
    ) -> Result<Ref<'_, S>, S::Error> {
        self.do_resolve::<S, _, _>(parameter, |value_slot| value_slot.state_ref())
    }

    /// Resolves (creates or retrieves) a mutable reference to a state.
    ///
    /// If the state does not exist, it will be initialized in place.
    ///
    /// # Panics
    ///
    /// - If the state is currently being initialized.
    /// - If there are outstanding immutable or mutable references.
    ///
    /// # Errors
    ///
    /// Returns the states [`S::Error`] if the state’s initialization fails.
    ///
    /// # Warning
    ///
    /// Be cautious of circular dependencies between states.
    pub fn resolve_with_mut<S: State>(
        &self,
        parameter: S::Parameter<'_>,
    ) -> Result<RefMut<'_, S>, S::Error> {
        self.do_resolve::<S, _, _>(parameter, |value_slot| value_slot.state_mut())
    }
}

impl StateRegistry {
    /// Convenience wrapper for [`Self::set_with`] using a default parameter.
    pub fn set<S: State>(&self, value: impl Into<Box<S>>)
    where
        for<'a> S::Parameter<'a>: Default,
    {
        self.set_with(Default::default(), value)
    }

    /// Convenience wrapper for [`Self::get_with`] using a default parameter.
    pub fn get<S: State>(&self) -> Option<Ref<'_, S>>
    where
        for<'a> S::Parameter<'a>: Default,
    {
        self.get_with(Default::default())
    }

    /// Convenience wrapper for [`Self::get_with_mut`] using a default parameter.
    pub fn get_mut<S: State>(&self) -> Option<RefMut<'_, S>>
    where
        for<'a> S::Parameter<'a>: Default,
    {
        self.get_with_mut(Default::default())
    }

    /// Convenience wrapper for [`Self::resolve_with`] using a default parameter.
    pub fn resolve<S: State>(&self) -> Result<Ref<'_, S>, S::Error>
    where
        for<'a> S::Parameter<'a>: Default,
    {
        self.resolve_with(Default::default())
    }

    /// Convenience wrapper for [`Self::resolve_with_mut`] using a default parameter.
    pub fn resolve_mut<S: State>(&self) -> Result<RefMut<'_, S>, S::Error>
    where
        for<'a> S::Parameter<'a>: Default,
    {
        self.resolve_with_mut(Default::default())
    }
}

#[cfg(test)]
mod test {
    use std::convert::Infallible;

    use crate::{
        registry::StateRegistry,
        State,
    };

    #[test]
    fn recursive_resolve() {
        struct StateA;
        impl State for StateA {
            type Error = Infallible;
            type Parameter<'a> = ();

            fn create(
                _registry: &StateRegistry,
                _param: Self::Parameter<'_>,
            ) -> Result<Self, Self::Error> {
                Ok(Self {})
            }
        }

        struct StateB;
        impl State for StateB {
            type Error = Infallible;
            type Parameter<'a> = ();

            fn create(
                registry: &StateRegistry,
                _param: Self::Parameter<'_>,
            ) -> Result<Self, Self::Error> {
                assert!(registry.get::<StateA>().is_none());
                assert!(registry.get_mut::<StateA>().is_none());

                {
                    let _statea = registry.resolve::<StateA>().unwrap();
                    assert!(registry.get::<StateA>().is_some());
                }

                assert!(registry.get_mut::<StateA>().is_some());
                Ok(Self)
            }
        }

        let registry = StateRegistry::new(0x10);
        let _stateb = registry.resolve::<StateB>().unwrap();
    }

    #[test]
    fn get_set() {
        #[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
        struct MyState {
            value: u64,
        }

        impl State for MyState {
            type Error = Infallible;
            type Parameter<'a> = u64;

            fn create(
                _registry: &StateRegistry,
                param: Self::Parameter<'_>,
            ) -> Result<Self, Self::Error> {
                println!("MyState {param} created");
                Ok(Self { value: param })
            }
        }

        impl Drop for MyState {
            fn drop(&mut self) {
                println!("MyState {} destroyed", self.value);
            }
        }

        let registry = StateRegistry::new(0x100);
        registry.set_with(42, MyState { value: 42 });
        registry.set_with(44, MyState { value: 44 });

        let value = registry.get_with::<MyState>(42).expect("to be present");
        assert_eq!(*value, MyState { value: 42 });

        let value = registry.get_with::<MyState>(44).expect("to be present");
        assert_eq!(*value, MyState { value: 44 });

        assert!(registry.get_with::<MyState>(40).is_none());
    }
}
