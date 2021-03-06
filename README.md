# ::\<automa\>
### A state machine builder for creating deterministic state machines

[![crates.io](https://img.shields.io/crates/v/automafish.svg)](https://crates.io/crates/automafish)
[![Docs](https://docs.rs/automafish/badge.svg)](https://docs.rs/automafish)

Automafish is a state machine builder for turning [nondeterministic finite automata] into [deterministic finite automata]. Its primary use case is driving the selector logic of [metamorfish] to enable mutation of [protofish] values in [proxide].

[nondeterministic finite automata]: https://en.wikipedia.org/wiki/Nondeterministic_finite_automaton
[deterministic finite automata]: https://en.wikipedia.org/wiki/Deterministic_finite_automaton
[metamorfish]: https://github.com/Rantanen/metamorfish
[protofish]: https://github.com/Rantanen/protofish
[proxide]: https://github.com/Rantanen/proxide

```rust
use std::iter::FromIterator;
use automafish::{Builder, State, Transition, Criteria, Condition};

let mut builder : Builder<Condition<char>, &mut dyn FnMut(&mut char)> = Builder::new();

// Set up an automata that capitalizes first character of a word.
let mut upper_case = |mut c: &mut char| { c.make_ascii_uppercase(); };
let wait_not_space = builder.create_initial_state();
let first_not_space = builder.add_state(State::with_action(&mut upper_case));
let wait_for_space = builder.add_state(State::new());

builder.add_transition(Transition::new(
    wait_not_space, Condition::Is(vec![' ']), wait_not_space));
builder.add_transition(Transition::new(
    wait_not_space, Condition::Not(vec![' ']), first_not_space));
builder.add_transition(Transition::new(
    first_not_space, Condition::Not(vec![' ']), wait_for_space));
builder.add_transition(Transition::new(
    first_not_space, Condition::Is(vec![' ']), wait_not_space));
builder.add_transition(Transition::new(
    wait_for_space, Condition::Not(vec![' ']), wait_for_space));
builder.add_transition(Transition::new(
    wait_for_space, Condition::Is(vec![' ']), wait_not_space));

// Set up an automata that counts all exclamation marks.
// This automata modifies a value outside the state machine.
let mut exclamations = 0;
let mut exclamation_counter = |_: &mut char| { exclamations += 1; };
let wait_exclamation = builder.create_initial_state();
let exclamation = builder.add_state(State::with_action(&mut exclamation_counter));

builder.add_transition(Transition::new(
    wait_exclamation, Condition::Any, wait_exclamation));
builder.add_transition(Transition::new(
    wait_exclamation, Condition::Is(vec!['!']), exclamation));

// Build the machine.
let mut machine = builder.build();

// Execute the machine on an input string.
let mut current_state = machine.start();
let mut input : Vec<char> = "hello world! this is rust!".chars().collect();
for i in &mut input {
    current_state = machine.step_and_execute_mut(current_state, i);
}

let output : String = String::from_iter(input);

assert_eq!("Hello World! This Is Rust!", output);
assert_eq!(2, exclamations);
```

## Related crates

- **[Proxide]** - A debugging proxy for HTTP/2 and especially gRPC traffic. The
  primary application using Automafish in its scripting implementation through
  Metamorfish.
- **[Metamorfish]** - A selector-based mutation engine intended to allow easy
  definition of operations to modify data structures intercepted by Proxide.
  Uses Automafish to implement state machines for the selectors.

[Proxide]: https://github.com/Rantanen/proxide
[Metamorfish]: https://github.com/Rantanen/metamorfish

In addition there seem to be other generic state machine crates that I
discovered while looking into options. If you ended up here looking for one,
you might be interested in the following crates as well. Note that I haven't
personally tested any of these crates.

- [automata] - A general purpose automata crate that, based on its description,
  implements DFA/NFA/Regular Expression conversion operations. There is a long
  list of planned features, although the development seems to have been
  abandoned.
- [nifty] - A crate for generating DFAs. Based on its readme, the macro-based
  approach seems quite neat for static DFAs. My use case required runtime
  specification of DFAs based on user scripts, which made me move away from
  this one. The crate seems to also be limited to DFAs with no support for
  building them from NFAs.
- [rustomaton] - An automaton manipulation library. Seems to include various
  conversion functions between various kinds of automatons (including DFA and
  NFA). However the execution phase of automatons seems to require all of the
  input beforehand so I wasn't sure whether it would suit my needs for a Moore
  machine that is able to execute actions in various intermediate states.

[automata]: https://crates.io/crates/automata
[nifty]: https://crates.io/crates/nifty
[rustomaton]: https://crates.io/crates/rustomaton

## Goals

The only current goal for Automafish is providing a somewhat efficient state
machine implementation for Metamorfish.

Use cases outside of those required by Metamorfish are definitely not out of
scope, but currently it's unlikely I'll be adding new features to Automafish
that Metamorfish doesn't need on my own. Feature and pull requests are
definitely welcome though! It's just that without any other priorities,
Metamorfish and Proxide itself are more interesting to me. :)

## Maybe in the future

Defining custom `Criteria` is somewhat painful currently with the need to
resolve intersections and differences for such criteria. I would simplify the
process of handling `Criteria`, but currently I don't really know how to build
the powersets without (at the very least) the intersection handling.

Then again, I haven't really looked into available algorithms for such use
cases.
