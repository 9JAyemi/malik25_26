// SVA for PosClockedOneShot
// Place inside the module or bind into it

default clocking cb @(posedge CLOCK); endclocking

// Basic sanity
assert property (cb !$isunknown({Reset, InputPulse, State, OneShot}));

// Synchronous reset behavior
assert property (cb Reset |-> (State==State0 && OneShot==1'b0));

// Illegal/unreachable state (State2) must not be entered in normal operation
assert property (cb disable iff (Reset) State != State2);

// Input low forces idle on the next cycle from any state
assert property (cb disable iff (Reset) !$past(InputPulse) |-> (State==State0 && OneShot==1'b0));

// High input transitions and output mapping
assert property (cb disable iff (Reset) $past(InputPulse) && $past(State)==State0 |-> (State==State1 && OneShot==1'b1));
assert property (cb disable iff (Reset) $past(InputPulse) && $past(State)==State1 |-> (State==State3 && OneShot==1'b0));
assert property (cb disable iff (Reset) $past(InputPulse) && $past(State)==State3 |-> (State==State3 && OneShot==1'b1));

// Stray/forced State2 must recover to idle next cycle regardless of input
assert property (cb disable iff (Reset) $past(State)==State2 |-> (State==State0 && OneShot==1'b0));

// OneShot equivalence: only asserted when previous cycle had InputPulse=1 and prev state in {State0,State3}
assert property (cb disable iff (Reset)
  OneShot == ($past(InputPulse) && ($past(State) inside {State0,State3})));

// Coverage
cover property (cb Reset ##1 !Reset);                                    // reset sequence
cover property (cb disable iff (Reset) $past(State)==State0 && $past(InputPulse) && OneShot);          // S0 -> S1, OneShot=1
cover property (cb disable iff (Reset) $past(State)==State1 && $past(InputPulse) && State==State3 && !OneShot); // S1 -> S3 on sustained high
cover property (cb disable iff (Reset) $past(State)==State3 && $past(InputPulse) && State==State3 && OneShot);   // S3 self-loop with OneShot=1
cover property (cb disable iff (Reset) $past(State)==State3 && !$past(InputPulse) && State==State0 && !OneShot); // return to idle on input low
cover property (cb State==State2); // should remain uncovered (unreachable)