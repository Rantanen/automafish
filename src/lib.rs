//! Automafish DFA builder
//! ======================
//! **Makes state machines that do things**
//!
//! Automafish can be used to optimize state machines defined through states and overlapping
//! transitions into more effective-to-evaluate deterministic forms.
//!
//! In technical terms Automafish takes [nondeterministic] [Moore machines] and creates a
//! [deterministic state machine] for it through [powerset construction].
//!
//! [deterministic state machine]: https://en.wikipedia.org/wiki/Deterministic_finite_automaton
//! [nondeterministic]: https://en.wikipedia.org/wiki/Nondeterministic_finite_automaton
//! [Moore machines]: https://en.wikipedia.org/wiki/Moore_machine
//! [powerset construction]: https://en.wikipedia.org/wiki/Powerset_construction
//!
//! # Example
//!
//! ```
//! # // Update README when changing the example here.
//! # env_logger::init();
//! use std::iter::FromIterator;
//! use automafish::{Builder, State, Transition, Criteria, Condition};
//!
//! let mut builder : Builder<Condition<char>, &mut dyn FnMut(&mut char)> = Builder::new();
//!
//! // Set up an automata that capitalizes first character of a word.
//! let mut upper_case = |mut c: &mut char| { c.make_ascii_uppercase(); };
//! let wait_not_space = builder.create_initial_state();
//! let first_not_space = builder.add_state(State::with_action(&mut upper_case));
//! let wait_for_space = builder.add_state(State::new());
//!
//! builder.add_transition(Transition::new(
//!     wait_not_space, Condition::Is(vec![' ']), wait_not_space));
//! builder.add_transition(Transition::new(
//!     wait_not_space, Condition::Not(vec![' ']), first_not_space));
//! builder.add_transition(Transition::new(
//!     first_not_space, Condition::Not(vec![' ']), wait_for_space));
//! builder.add_transition(Transition::new(
//!     first_not_space, Condition::Is(vec![' ']), wait_not_space));
//! builder.add_transition(Transition::new(
//!     wait_for_space, Condition::Not(vec![' ']), wait_for_space));
//! builder.add_transition(Transition::new(
//!     wait_for_space, Condition::Is(vec![' ']), wait_not_space));
//!
//! // Set up an automata that counts all exclamation marks.
//! // This automata modifies a value outside the state machine.
//! let mut exclamations = 0;
//! let mut exclamation_counter = |_: &mut char| { exclamations += 1; };
//! let wait_exclamation = builder.create_initial_state();
//! let exclamation = builder.add_state(State::with_action(&mut exclamation_counter));
//!
//! builder.add_transition(Transition::new(
//!     wait_exclamation, Condition::Any, wait_exclamation));
//! builder.add_transition(Transition::new(
//!     wait_exclamation, Condition::Is(vec!['!']), exclamation));
//!
//! // Build the machine.
//! let mut machine = builder.build();
//!
//! // Execute the machine on an input string.
//! let mut current_state = machine.start();
//! let mut input : Vec<char> = "hello world! this is rust!".chars().collect();
//! for i in &mut input {
//!     current_state = machine.step_and_execute_mut(current_state, i);
//! }
//!
//! let output : String = String::from_iter(input);
//!
//! assert_eq!("Hello World! This Is Rust!", output);
//! assert_eq!(2, exclamations);
//! ```
#![warn(missing_docs)]

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::hash::Hash;
use std::sync::atomic::{AtomicUsize, Ordering};

static ID_COUNTER: AtomicUsize = AtomicUsize::new(1);

mod refs {
    use super::*;
    use std::ops::{Index, IndexMut};
    macro_rules! ImplIndex {
        (<$($generics:tt),*> $idx_ty:ty => $target_ty:ty) => {
            ImplIndex! { @ ($($generics),*) $idx_ty => $target_ty }
        };
        ($idx_ty:ty => $target_ty:ty) => {
            ImplIndex! { @ () $idx_ty => $target_ty }
        };
        ( @ ($($generics:tt),*) $idx_ty:ty => $target_ty:ty) => {
            impl<$($generics),*> Index<$idx_ty> for Vec<$target_ty> {
                type Output = $target_ty;
                fn index(&self, idx: $idx_ty) -> &Self::Output {
                    &self[idx.idx]
                }
            }
            impl<$($generics),*> IndexMut<$idx_ty> for Vec<$target_ty> {
                fn index_mut(&mut self, idx: $idx_ty) -> &mut Self::Output {
                    &mut self[idx.idx]
                }
            }
            impl $idx_ty {
                #[allow(dead_code)]
                pub(super) fn new_unchecked(m: usize, idx: usize) -> Self {
                    Self { m, idx }
                }

                #[allow(dead_code)]
                pub(super) fn next_ref<$($generics),*>(m: usize, v: &[$target_ty]) -> Self {
                    Self { m, idx: v.len() }
                }

                #[allow(dead_code)]
                pub(crate) fn uninit() -> Self {
                    Self { m: usize::MAX, idx: usize::MAX }
                }

                #[allow(dead_code)]
                pub(crate) fn assert_same_machine(&self, other: Self) {
                    if self.m != other.m { panic!("Incompatible machine") }
                }

                #[allow(dead_code)]
                pub(crate) fn assert_machine(&self, m: usize) {
                    if self.m != m { panic!("Wrong machine") }
                }
            }
            impl std::fmt::Debug for $idx_ty {
                fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                    f.debug_struct(stringify!($idx_ty))
                        .field("#", &self.idx)
                        .finish()
                }
            }
        };
    }

    #[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
    pub struct MachineState {
        m: usize,
        idx: usize,
    }

    #[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
    pub struct StateRef {
        m: usize,
        idx: usize,
    }

    #[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
    pub struct TransitionRef {
        m: usize,
        idx: usize,
    }

    #[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
    pub(super) struct ActionRef {
        m: usize,
        idx: usize,
    }

    #[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
    pub(super) struct MixedTransitionRef {
        m: usize,
        idx: usize,
    }

    #[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
    pub(super) struct MixedStateKey(BTreeSet<StateRef>);
    impl MixedStateKey {
        pub fn new<I>(i: I) -> Self
        where
            I: IntoIterator<Item = StateRef>,
        {
            use std::iter::FromIterator;
            Self(BTreeSet::from_iter(i))
        }

        pub fn empty() -> Self {
            Self(BTreeSet::new())
        }

        pub fn is_empty(&self) -> bool {
            self.0.is_empty()
        }

        pub fn extend(&mut self, new: MixedStateKey) {
            self.0.extend(new.0);
        }

        pub fn add(&mut self, new: StateRef) {
            self.0.insert(new);
        }
    }

    impl<'a> IntoIterator for &'a MixedStateKey {
        type Item = &'a StateRef;
        type IntoIter = <&'a BTreeSet<StateRef> as IntoIterator>::IntoIter;
        fn into_iter(self) -> Self::IntoIter {
            (&self.0).iter()
        }
    }

    ImplIndex! { <C> MachineState => FinalState<C> }
    ImplIndex! { <T> StateRef => State<T> }
    ImplIndex! { <T> TransitionRef => Transition<T> }
    ImplIndex! { <T> ActionRef => T }
    ImplIndex! { <T> MixedTransitionRef => MixedTransition<T> }
}
use refs::{ActionRef, MachineState, MixedStateKey, StateRef, TransitionRef};

/// A compiled state machine.
///
/// The `StateMachine` can be created with the [`Builder`].
#[derive(Debug)]
pub struct StateMachine<TCriteria, TAction> {
    machine_id: usize,
    initial_state: MachineState,
    actions: Vec<TAction>,
    states: Vec<FinalState<TCriteria>>,
}

#[derive(Debug)]
struct FinalState<TCriteria> {
    actions: Vec<ActionRef>,
    transitions: Vec<(TCriteria, MachineState)>,
}

/// A state machine state.
///
/// `State` is used to define possible states when building a [`StateMachine`]
/// with a [`Builder`]. Each state may contain actions that are executed when
/// the state is reached.
#[derive(Debug)]
pub struct State<TAction> {
    self_ref: StateRef,
    actions: Vec<TAction>,
    transitions: Vec<TransitionRef>,
}

#[derive(Debug)]
struct MixedState<TCriteria> {
    states: MixedStateKey,
    transitions: Vec<MixedTransition<TCriteria>>,
}

/// A state machine transition.
///
/// `Transition` is used to define possible transition between different [`State`]. The transitions
/// are triggered based on some [`Criteria`] when the state machine is being executed.
#[derive(Debug)]
pub struct Transition<TCriteria> {
    source: StateRef,
    target: StateRef,
    criteria: TCriteria,
}

/// A state machine builder.
///
/// The `Builder` allows defining the state machine as a [Nondeterministic Finite Automaton] using
/// [`Self::add_state`] and [`Self::add_transition`] methods. Once the state machine is described in such a way
/// the final [`StateMachine`] can be built with the [`Self::build`] method.
///
/// [Nondeterministic Finite Automaton]: https://en.wikipedia.org/wiki/Nondeterministic_finite_automaton
#[derive(Debug)]
pub struct Builder<TCriteria, TAction> {
    machine_id: usize,
    initial_states: Vec<StateRef>,
    states: Vec<State<TAction>>,
    transitions: Vec<Transition<TCriteria>>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct MixedTransition<TCriteria> {
    criteria: TCriteria,
    source: MixedStateKey,
    target: MixedStateKey,
}

/// A trait defining transition criteria.
///
/// The criteria defines a condition that the [`StateMachine`] input needs to
/// match for a specific state transition to occur. The input type of the state
/// machine is indirectly defined by the [`Self::Input`] of the state machine criteria.
pub trait Criteria: Clone + PartialEq + Eq + Hash {
    /// Input type for the state machien criteria.
    type Input;

    /// Checks whether a given input is a match for a specific criteria.
    fn is_match(&self, input: &Self::Input) -> bool;

    /// Checks if the `Criteria` represents an empty criteria that doesn't match any input.
    ///
    /// Recognizing empty `Criteria` allows the [`Builder`] to simplify the final [`StateMachine`].
    /// Returning `false` in case the `Criteria` _is_ empty does not break the actual state
    /// processing, but will result in extra states and state transitions being included in the
    /// final `StateMachine`.
    fn is_empty(&self) -> bool;

    /// The evaluation order of the `Criteria` defines the order in which the state transitiosn are
    /// evaluated. Criteria with smaller evaluation order is processed first.
    ///
    /// This allows some leeway in how accurate the [`Self::and`] and [`Self::not`] implementations are. See
    /// [`Self::not`] for more details.
    fn evaluation_order(&self) -> usize {
        0
    }

    /// Combines two `Criteria` together.
    ///
    /// The [`Builder`] will use this method when calculating state transitions in the final
    /// [`StateMachine`] between deterministic states representing several nondeterministic states
    /// defined in the [`Builder`].
    ///
    /// The `Builder` will only invoke this method with `other` being a criteria defined in the
    /// _original_ state transitions by hand. An output of `and` or `not` is never used as the
    /// `other` parameter.
    ///
    /// # Example
    ///
    /// ```
    /// # use std::collections::BTreeSet;
    /// # use automafish::Criteria;
    /// # use std::hash::Hash;
    /// #[derive(Clone, PartialEq, Eq, Hash)]
    /// struct OneOf(BTreeSet<u32>);
    /// impl Criteria for OneOf {
    /// #   type Input = u32;
    /// #   fn is_match(&self, input: &Self::Input) -> bool { self.0.contains(input) }
    /// #   fn is_empty(&self) -> bool { false }
    /// #   fn not(&self, other: &Self) -> Self { unimplemented!() }
    /// #   fn any() -> Self { unimplemented!() }
    ///     fn and(&self, other: &Self) -> Self {
    ///         OneOf(self.0.intersection(&other.0).copied().collect())
    ///     }
    ///
    /// // ... rest of the required methods.
    /// }
    ///
    /// let small = OneOf(vec![ 1, 2, 3, 4 ].into_iter().collect());
    /// let even = OneOf(vec![ 2, 4, 6, 8 ].into_iter().collect());
    ///
    /// let small_and_even = small.and(&even);
    ///
    /// let input = 4;
    /// assert_eq!(
    ///     small.is_match(&input) && even.is_match(&input),
    ///     small_and_even.is_match(&input));
    /// ```
    fn and(&self, other: &Self) -> Self;

    /// Calculates a difference criteria that matches `self` but not `other`.
    ///
    /// The [`Builder`] will use this method when calculating state transitions in the final
    /// [`StateMachine`] between deterministic states representing several nondeterministic states
    /// defined in the [`Builder`].
    ///
    /// The `Builder` will only invoke this method with `other` being a criteria defined in the
    /// _original_ state transitions by hand. An output of `and` or `not` is never used as the
    /// `other` parameter.
    ///
    /// This allows for some simplification in the resulting state. The `Builder` asking for
    /// criteria such as `a.not(b)` occurs in a situation where there is criteria `b` in some state
    /// transition that should take priority over the one for which the `a.not(b)` criteria
    /// applies. This means that as long as `a.not(b)` criteria has a lower evaluation order, it's
    /// perfectly valid to return `a` as a result of that `not` operation. An example of this would
    /// be the [`Self::any`] state, which can be returned as is, as long as it has the lowest evaluation
    /// order.
    fn not(&self, other: &Self) -> Self;

    /// A default criteria that matches everything.
    ///
    /// In general this criteria shouldn't be used for `is_match` unless it appears explicitly in
    /// the user-specified [`Transition`] definitions. Instead the any-state is used as a building
    /// block when the [`Builder`] constructs the final transitions for the resulting deterministic
    /// finite automaton. The final states are `any()` combined with one or more `and(..)` and zero
    /// or more `not(..)`.
    fn any() -> Self;
}

/// Action that may be executed when entering a state.
///
/// See [`ActionMut`] if you need an action that may mutate its internal state. The `Action` is
/// implemented for `Box<Fn(T)>` by default.
pub trait Action {
    /// Input type for the action.
    type Input;

    /// Perform the action in the input.
    ///
    /// Note that the `input` takes the input type as a reference to allow multiple actions to be
    /// executed on it if necessary. This doesn't prevent mutating the input though, since the
    /// `Input` itself can be defined as `&mut Foo`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use automafish::Action;
    /// struct IncrementValue;
    /// impl Action for IncrementValue {
    ///     type Input = u32;
    ///     fn execute(&self, input: &mut Self::Input) {
    ///         *input += 1;
    ///     }
    /// }
    /// ```
    fn execute(&self, input: &mut Self::Input);
}

/// Action that may be executed when entering a state and may mutate its inner state.
///
/// The `ActionMut` is implemented for `Box<FnMut(T)>` by default.
pub trait ActionMut {
    /// Input type for the action.
    type Input;

    /// Perform the action in the input.
    ///
    /// Note that the `input` takes the input type as a reference to allow multiple actions to be
    /// executed on it if necessary. This doesn't prevent mutating the input though, since the
    /// `Input` itself can be defined as `&mut Foo`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use automafish::ActionMut;
    /// struct IncrementValue<'a> { buffer: &'a mut Vec<u32> }
    /// impl<'a> ActionMut for IncrementValue<'a> {
    ///     type Input = u32;
    ///     fn execute_mut(&mut self, input: &mut Self::Input) {
    ///         self.buffer.push(*input);
    ///     }
    /// }
    /// ```
    fn execute_mut(&mut self, input: &mut Self::Input);
}

impl<TCriteria, TAction> Builder<TCriteria, TAction>
where
    TCriteria: Criteria,
{
    /// Create a new `Builder`
    pub fn new() -> Self {
        Self {
            machine_id: ID_COUNTER.fetch_add(1, Ordering::Relaxed),
            initial_states: vec![],
            states: vec![],
            transitions: vec![],
        }
    }

    /// Create a new initial state.
    ///
    /// Each initial state is unique in regards to their transitions. Multiple initial states may
    /// be used to separate automata that might have different transitions to their initial states.
    pub fn create_initial_state(&mut self) -> StateRef {
        let state_ref = StateRef::next_ref(self.machine_id, &self.states);
        self.states.push(State::new());
        self.initial_states.push(state_ref);
        state_ref
    }

    /// Add a new state to the builder.
    pub fn add_state(&mut self, state: State<TAction>) -> StateRef {
        let mut state = state;
        state.self_ref = StateRef::next_ref(self.machine_id, &self.states);
        let state_ref = state.self_ref;
        self.states.push(state);
        state_ref
    }

    /// Add a new transition between builder states.
    pub fn add_transition(&mut self, transition: Transition<TCriteria>) {
        transition.source.assert_machine(self.machine_id);

        let transition_ref = TransitionRef::next_ref(self.machine_id, &self.transitions);
        let source = &mut self.states[transition.source];
        source.transitions.push(transition_ref);
        self.transitions.push(transition);
    }

    /// Consume the builder, returning a final [`StateMachine`].
    pub fn build(self) -> StateMachine<TCriteria, TAction> {
        // Diagnostic information on the original NFA state counts.
        let nfa_state_count = self.states.len();
        let nfa_transition_count = self.transitions.len();

        // Start a collection of all states.
        let mut all_states: BTreeMap<MixedStateKey, MixedState<TCriteria>> = BTreeMap::new();

        // Insert the initial state to the queue to get things started.
        let initial_state_key = MixedStateKey::new(self.initial_states);
        let mut processing_queue = vec![initial_state_key.clone()];
        all_states.insert(
            initial_state_key.clone(),
            MixedState {
                states: initial_state_key.clone(),
                transitions: vec![],
            },
        );

        // We'll need to keep processing items in the queue until we run out of items to process.
        // Each step might add multiple new states to the processing_queue, but at some point we
        // should stop encountering new states as there's only so many possible NFA state
        // combinations we can get (although that number is 2^n, where n is the original NFA state
        // count).
        let mut processing_cursor = 0;
        while processing_cursor < processing_queue.len() {
            let current_key = processing_queue[processing_cursor].clone();
            log::trace!("Processing state {:?}", current_key);

            // Create all expanded transitions.
            //
            // We'll start with a dummy any-transition just to bootstrap the `expand_transitions`
            // algorithm that uses the existing transitions as the base.  Normally this dummy
            // transition is stopped later since it has no target states - unless of course one of
            // the user specified transitions is a `any()` transition.
            let mut expanded_transitions = vec![MixedTransition {
                criteria: TCriteria::any(),
                source: current_key.clone(),
                target: MixedStateKey::empty(),
            }];

            // Construct the transitions by iterating all the possible transitions from the states
            // represented by this `MixedState`.
            for o_ref in &current_key {
                let original = &self.states[*o_ref];
                for t_ref in &original.transitions {
                    let transition = &self.transitions[*t_ref];
                    expand_transitions(&mut expanded_transitions, transition);
                }
            }

            // Merge transitions that use the same criteria. The expansion above might have
            // resulted in multiple equal criteria through different means (A - B and A - C, when
            // A, B and C don't overlap). Here we ensure that such transitions result in a combined
            // mixed state.
            let mut expanded_transitions_map = HashMap::new();
            for t in expanded_transitions {
                let entry = expanded_transitions_map
                    .entry(t.criteria.clone())
                    .or_insert(MixedTransition {
                        criteria: t.criteria,
                        source: current_key.clone(),
                        target: MixedStateKey::empty(),
                    });
                entry.target.extend(t.target);
            }

            // Drop the transitions that have empty criteria or targets.
            let expanded_transitions: Vec<_> = expanded_transitions_map
                .into_iter()
                .map(|(_, t)| t)
                .filter(|t| !t.criteria.is_empty() && !t.target.is_empty())
                .collect();

            // Now that we have all the possible transitions, we'll need to see if
            // we found any new target states. These are added to the end of the processing queue
            // so we'll process them in the future.
            //
            // Unless there's a bug somewhere, at some point we'll start exhausting the list of
            // possible target states and stop adding new ones here, allowing the remaining
            // processing backlog to run out and this while-loop to terminate.
            for t in &expanded_transitions {
                if all_states.contains_key(&t.target) {
                    continue;
                }

                // Encountered a state that isn't in the queue yet.
                all_states.insert(
                    t.target.clone(),
                    MixedState {
                        states: t.target.clone(),
                        transitions: vec![],
                    },
                );
                processing_queue.push(t.target.clone());
            }

            all_states.get_mut(&current_key).unwrap().transitions = expanded_transitions;
            processing_cursor += 1;
        }

        // All states have been processed. Now we'll just need to construct the final state
        // machine.
        let mut machine = StateMachine::<TCriteria, TAction> {
            machine_id: ID_COUNTER.fetch_add(1, Ordering::Relaxed),
            initial_state: MachineState::uninit(),
            actions: vec![],
            states: vec![],
        };

        // Resolve all state refs. The actions are defined on the original states, but to avoid
        // requiring `Clone` on the `TAction`, we'll move them to just one vector which is indexed
        // by `ActionRef`. However we'll need to calculate the refs beforehand, since we can't move
        // the actions out of the `self.states` yet since partial moves out of `Vec` are not
        // supported.
        let mut actions_to_final: HashMap<(StateRef, usize), ActionRef> = HashMap::new();
        for s in &self.states {
            for i in 0..s.actions.len() {
                let action_ref = ActionRef::new_unchecked(self.machine_id, actions_to_final.len());
                actions_to_final.insert((s.self_ref, i), action_ref);
            }
        }

        // Register all final states on the machine and construct a mapping between mixed state
        // keys and final machine states. We'll need to resolve the `MachineState` references for
        // use in the transitions when setting up individual states later.
        let mut mixed_to_final: BTreeMap<MixedStateKey, MachineState> = BTreeMap::new();
        for key in all_states.keys() {
            mixed_to_final.insert(
                key.clone(),
                MachineState::next_ref(machine.machine_id, &machine.states),
            );

            // For now just add a place holder for the state. We'll fill this later once we have
            // resolved `mixed_to_final` mappings for all states.
            machine.states.push(FinalState {
                actions: vec![],
                transitions: vec![],
            });
        }

        // Finally set up the final machine states based on the information resolved earlier.
        let mut dfa_transition_count = 0;
        for (mixed_key, mut mixed_state) in all_states {
            // Reference to the for-now somewhat uninitialized final state.
            let final_state = &mut machine.states[mixed_to_final[&mixed_key]];

            // Fill in the action refs based on the actions of the original states this final state
            // represents.
            for original_ref in &mixed_key {
                let original_state = &self.states[*original_ref];
                for i in 0..original_state.actions.len() {
                    final_state
                        .actions
                        .push(actions_to_final[&(*original_ref, i)]);
                }
            }

            // Fill in the transitions. Since this is now the place used for the actual evaluation
            // later, we need to ensure the transitions are sorted by the evaluation order.
            mixed_state
                .transitions
                .sort_by_key(|t| t.criteria.evaluation_order());
            for t in mixed_state.transitions {
                final_state
                    .transitions
                    .push((t.criteria, mixed_to_final[&t.target]));
            }

            dfa_transition_count += final_state.transitions.len();
        }

        // Finally move the actions into the final StateMachine. The order here needs to follow the
        // same order we used earlier when resolving the `ActionRef`s used to refer to these
        // actions in the `machine.states`.
        //
        // This consumes the builder `self.states`, which is why we had to wait till now to do it.
        for s in self.states {
            for a in s.actions {
                machine.actions.push(a)
            }
        }

        let dfa_state_count = machine.states.len();
        log::trace!(
            "Built DFA with {} states, {} transitions from NFA of {} states, {} transitions",
            dfa_state_count,
            dfa_transition_count,
            nfa_state_count,
            nfa_transition_count
        );

        machine.initial_state = mixed_to_final[&initial_state_key];
        machine
    }
}

impl<TCriteria, TAction> Default for Builder<TCriteria, TAction>
where
    TCriteria: Criteria,
{
    fn default() -> Self { Self::new() }
}

fn expand_transitions<TCriteria>(
    transitions: &mut Vec<MixedTransition<TCriteria>>,
    transition: &Transition<TCriteria>,
) where
    TCriteria: Criteria,
{
    // Handle And-case first since here we can perform filtering on the fly
    // without having to deal with shifting elements in the Vec.
    // The And-case is more likely to result in empty criteria so dropping
    // criteria is more likely in this case.
    let and = transitions
        .iter()
        .filter_map(|t| {
            let criteria = t.criteria.and(&transition.criteria);
            match !criteria.is_empty() {
                true => {
                    let mut new = t.clone();
                    new.target.add(transition.target);
                    new.criteria = criteria;
                    Some(new)
                }
                false => None,
            }
        })
        .collect::<Vec<_>>();

    // Handle the Not-case by removing the new criteria from the existing ones.
    // This doesn't alter the target states.
    let mut i = 0;
    while i != transitions.len() {
        let t = &mut transitions[i];
        t.criteria = t.criteria.not(&transition.criteria);
        if t.criteria.is_empty() {
            transitions.remove(i);
        } else {
            i += 1;
        }
    }

    transitions.extend(and);
}

impl<TAction> State<TAction> {
    /// Create a new state with no action.
    pub fn new() -> Self {
        Self::new_impl(vec![])
    }

    /// Create a new state with an action.
    pub fn with_action(action: TAction) -> Self {
        Self::new_impl(vec![action])
    }

    /// Create a new state with actions.
    pub fn with_actions<T>(actions: T) -> Self
    where
        T: IntoIterator<Item = TAction>,
    {
        use std::iter::FromIterator;
        Self::new_impl(Vec::from_iter(actions))
    }

    fn new_impl(actions: Vec<TAction>) -> Self {
        Self {
            self_ref: StateRef::uninit(),
            actions,
            transitions: vec![],
        }
    }
}

impl<TAction> Default for State<TAction> {
    fn default() -> Self { Self::new() }
}

impl<TCriteria> Transition<TCriteria> {
    /// Create a new transition between states.
    pub fn new(source: StateRef, criteria: TCriteria, target: StateRef) -> Self {
        source.assert_same_machine(target);

        Self {
            source,
            criteria,
            target,
        }
    }
}

impl<TCriteria, TAction> StateMachine<TCriteria, TAction>
where
    TCriteria: Criteria,
{
    /// Acquires the initial state of the state machine.
    pub fn start(&self) -> MachineState {
        self.initial_state
    }

    /// Performs a step from the `current` machine state with the given `input`.
    pub fn step(&self, current: MachineState, input: &TCriteria::Input) -> MachineState {
        self.next_state(current, input)
    }

    fn next_state(&self, current: MachineState, input: &TCriteria::Input) -> MachineState {
        current.assert_machine(self.machine_id);

        let current_state = &self.states[current];
        for t in &current_state.transitions {
            if t.0.is_match(&input) {
                return t.1;
            }
        }

        self.start()
    }
}

impl<TCriteria, TAction> StateMachine<TCriteria, TAction>
where
    TAction: Action,
{
    /// Executes the actions of the `current` state with the given `input`.
    ///
    /// Use [`Self::execute_mut`] if the current `TAction` is an [`ActionMut`].
    pub fn execute(&self, current: MachineState, input: &mut TAction::Input) {
        for a in &self.states[current].actions {
            self.actions[*a].execute(input);
        }
    }
}

impl<TCriteria, TAction> StateMachine<TCriteria, TAction>
where
    TAction: ActionMut,
{
    /// Executes the actions of the `current` state with the given `input`.
    ///
    /// Use [`Self::execute`] if the current `TAction` is an [`Action`].
    pub fn execute_mut(&mut self, current: MachineState, input: &mut TAction::Input) {
        for a in &mut self.states[current].actions {
            self.actions[*a].execute_mut(input);
        }
    }
}

impl<TCriteria, TAction> StateMachine<TCriteria, TAction>
where
    TAction: Action,
    TCriteria: Criteria<Input = TAction::Input>,
{
    /// Performs a step from the current `state` and executes any actions based on the new state.
    ///
    /// This method is available only if the `TCriteria` and `TAction` have the same `Input` type
    /// and is equivalent to:
    ///
    /// ```ignore
    /// let next_state = machine.step(current_state, &input);
    /// machine.execute(current_state, &mut input);
    /// ```
    pub fn step_and_execute(
        &self,
        current: MachineState,
        input: &mut TAction::Input,
    ) -> MachineState {
        let next = self.step(current, input);
        self.execute(next, input);
        next
    }
}

impl<TCriteria, TAction> StateMachine<TCriteria, TAction>
where
    TAction: ActionMut,
    TCriteria: Criteria<Input = TAction::Input>,
{
    /// Performs a step from the current `state` and executes any actions based on the new state.
    ///
    /// This method is available only if the `TCriteria` and `TAction` have the same `Input` type
    /// and is equivalent to:
    ///
    /// ```ignore
    /// let next_state = machine.step(current_state, &input);
    /// machine.execute_mut(current_state, &mut input);
    /// ```
    pub fn step_and_execute_mut(
        &mut self,
        current: MachineState,
        input: &mut TAction::Input,
    ) -> MachineState {
        let next = self.step(current, input);
        self.execute_mut(next, input);
        next
    }
}

impl<T> Action for Box<dyn Fn(&mut T)> {
    type Input = T;
    fn execute(&self, input: &mut T) {
        self(input)
    }
}

impl<T> ActionMut for Box<dyn FnMut(&mut T)> {
    type Input = T;
    fn execute_mut(&mut self, input: &mut T) {
        self(input)
    }
}

impl<'a, T> ActionMut for &'a mut dyn FnMut(&mut T) {
    type Input = T;
    fn execute_mut(&mut self, input: &mut T) {
        self(input)
    }
}

/// A basic "is" or "is not" condition criteria.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Condition<T> {
    /// Matches when the input is one of the values in the Vec.
    Is(Vec<T>),

    /// Matches when the input isn't one of the values in the Vec.
    Not(Vec<T>),

    /// Matches any value.
    Any,

    /// Matches no value.
    None,
}

impl<T: Clone + Copy + PartialEq + Eq + Hash> Criteria for Condition<T> {
    type Input = T;
    fn is_match(&self, i: &Self::Input) -> bool {
        match self {
            Condition::Is(c) => c.contains(&i),
            Condition::Not(c) => !c.contains(&i),
            Condition::Any => true,
            Condition::None => false,
        }
    }

    fn and(&self, other: &Self) -> Self {
        if self == other {
            return self.clone();
        }
        match (self, other) {
            (Condition::Is(i), Condition::Not(n)) | (Condition::Not(n), Condition::Is(i)) => {
                let new: Vec<T> = i.iter().filter(|c| !n.contains(c)).copied().collect();
                if new.is_empty() {
                    Condition::None
                } else {
                    Condition::Is(new)
                }
            }
            (Condition::Not(a), Condition::Not(b)) => {
                let a: HashSet<T> = a.iter().copied().collect();
                let b: HashSet<T> = b.iter().copied().collect();
                let intersection: Vec<T> = a.intersection(&b).copied().collect();
                if intersection.is_empty() {
                    Condition::Any
                } else {
                    Condition::Not(intersection)
                }
            }
            (Condition::Is(_), Condition::Is(_)) => Condition::None,
            (Condition::None, _) | (_, Condition::None) => Condition::None,
            (o, Condition::Any) | (Condition::Any, o) => o.clone(),
        }
    }

    fn not(&self, other: &Self) -> Self {
        if self == other {
            return Condition::None;
        }
        match (self, other) {
            (Condition::Not(n), Condition::Is(i)) => {
                let mut new_not = n.clone();
                new_not.extend(i);
                Condition::Not(new_not)
            }
            (Condition::Any, Condition::Is(i)) => Condition::Not(i.clone()),
            (Condition::None, _) => Condition::None,
            (o, Condition::None) => o.clone(),
            (_, Condition::Any) => Condition::None,
            (o, Condition::Not(n)) => o.and(&Condition::Is(n.clone())),
            (Condition::Is(i), _) => Condition::Is(i.clone()),
        }
    }

    fn is_empty(&self) -> bool {
        self == &Condition::None
    }
    fn any() -> Self {
        Condition::Any
    }
    fn evaluation_order(&self) -> usize {
        match self {
            Condition::Any => 1,
            _ => 0,
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use test_env_log::test;

    #[test]
    fn testt() {
        let mut builder = Builder::<Option<BTreeSet<char>>, _>::new();
        let start = builder.create_initial_state();
        let first = builder.add_state(State::with_actions(vec!["S1"]));
        let second = builder.add_state(State::with_actions(vec!["S2"]));
        let third = builder.add_state(State::with_actions(vec!["S3"]));

        use std::iter::FromIterator;
        builder.add_transition(Transition::new(start, None, start));
        builder.add_transition(Transition::new(
            start,
            Some(BTreeSet::from_iter("ab".chars())),
            first,
        ));
        builder.add_transition(Transition::new(
            first,
            Some(BTreeSet::from_iter("c".chars())),
            second,
        ));
        builder.add_transition(Transition::new(second, None, second));
        builder.add_transition(Transition::new(
            second,
            Some(BTreeSet::from_iter("a".chars())),
            third,
        ));

        let machine = builder.build();

        let mut next = machine.start();
        for mut s in ['a', 'b', 'b', 'c', 'c', 'a', 'a', 'c'].iter().copied() {
            next = machine.step(next, &s);
            machine.execute(next, &mut s);
        }
    }

    impl Criteria for Option<BTreeSet<char>> {
        type Input = char;

        fn is_match(&self, input: &Self::Input) -> bool {
            match self {
                None => true,
                Some(set) => set.contains(input),
            }
        }

        fn is_empty(&self) -> bool {
            match self {
                None => false,
                Some(set) => set.len() == 0,
            }
        }

        fn evaluation_order(&self) -> usize {
            match self {
                Some(_) => 0,
                None => 1,
            }
        }

        fn and(&self, other: &Self) -> Self {
            match (self, other) {
                (None, None) => None,
                (None, s) | (s, None) => s.clone(),
                (Some(a), Some(b)) => Some(a.intersection(b).copied().collect()),
            }
        }

        fn not(&self, other: &Self) -> Self {
            match (self, other) {
                (_, None) => Some(BTreeSet::new()),
                (None, _) => None,
                (Some(a), Some(b)) => Some(a.difference(b).copied().collect()),
            }
        }

        fn any() -> Self {
            None
        }
    }

    impl Action for &'static str {
        type Input = char;
        fn execute(&self, _: &mut char) {
            println!("State: {}", self);
        }
    }
}
