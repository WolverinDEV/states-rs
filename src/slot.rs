use std::collections::{
    hash_map::Entry,
    HashMap,
};

use crate::{
    state::StateLookupKey,
    StateType,
};

#[derive(Debug)]
pub enum SlotState {
    Empty,
    Initializing,
    Occupied {
        state_type: StateType,
        lookup_key: StateLookupKey,
    },
}

pub struct SlotAllocator {
    index_lookup: HashMap<StateLookupKey, usize>,
    index_free_list: Vec<usize>,

    slots: Box<[SlotState]>,
}

impl SlotAllocator {
    pub fn new(capacity: usize) -> Self {
        let mut free_list = Vec::with_capacity(capacity);
        for index in (0..capacity).rev() {
            free_list.push(index);
        }

        let mut slots = Vec::with_capacity(capacity);
        slots.resize_with(capacity, || SlotState::Empty);

        Self {
            index_lookup: Default::default(),
            index_free_list: free_list,
            slots: slots.into_boxed_slice(),
        }
    }

    pub fn get_slot(&self, slot_index: usize) -> &SlotState {
        &self.slots[slot_index]
    }

    pub fn lookup_slot(&self, key: &StateLookupKey) -> Option<(usize, &SlotState)> {
        let index = *self.index_lookup.get(key)?;
        Some((index, &self.slots[index]))
    }

    pub fn allocate_slot(&mut self, key: StateLookupKey) -> (usize, &mut SlotState) {
        let index = match self.index_lookup.entry(key) {
            Entry::Occupied(entry) => *entry.get(),
            Entry::Vacant(entry) => {
                let index = self
                    .index_free_list
                    .pop()
                    .expect("state registry ran out of capacity");

                *entry.insert(index)
            }
        };

        (index, &mut self.slots[index])
    }

    pub fn promote_slot(&mut self, key: StateLookupKey, state_type: StateType) {
        let slot_index = *self.index_lookup.get(&key).expect("to be present");
        let slot_state = &mut self.slots[slot_index];

        debug_assert!(matches!(*slot_state, SlotState::Initializing));
        *slot_state = SlotState::Occupied {
            state_type,
            lookup_key: key,
        };
    }

    pub fn free_slot(&mut self, key: &StateLookupKey) {
        let index = match self.index_lookup.remove(key) {
            Some(index) => index,
            None => return,
        };
        self.index_free_list.push(index);
        self.slots[index] = SlotState::Empty;
    }
}
