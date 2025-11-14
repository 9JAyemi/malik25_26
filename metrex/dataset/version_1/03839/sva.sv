// Drop this SVA block inside module controller, or bind it to the instance.
// Focus: legal state, reset behavior, next-logic correctness, counter/update sequencing,
// handshakes/pulses, config writes, and minimal but meaningful coverage.

`ifdef ASSERT_ON

// Clocking/disables
default clocking cb @(posedge clock); endclocking
default disable iff (reset)

// ============ Basic structural checks ============

// State encoding must remain within defined set
assert property (state inside {IDLE, SAMPLE, DELAY, READ, READWAIT});

// Async reset effect sampled on clock
assert property (@(posedge clock) reset |-> (state==IDLE && !memoryWrite && !memoryLastWrite && !memoryRead));

// Registered outputs/state follow their combinational next_* on next cycle
assert property (state           == $past(next_state));
assert property (memoryWrite     == $past(next_memoryWrite));
assert property (memoryLastWrite == $past(next_memoryLastWrite));
assert property (memoryRead      == $past(next_memoryRead));
assert property (send            == $past(next_send));
assert property (counter         == $past(next_counter));

// memoryWrData captures dataIn each cycle
assert property (memoryWrData == $past(dataIn));

// No X on key state/outputs after reset
assert property (!$isunknown({state, memoryWrite, memoryLastWrite, memoryRead, send}));

// ============ Combinational next_* logic per state ============

// IDLE
assert property (state==IDLE |->
                 (next_counter==0 && next_memoryWrite && 
                  next_state==(run ? DELAY : (arm ? SAMPLE : IDLE))));

// SAMPLE
assert property (state==SAMPLE |->
                 (next_counter==0 && (next_memoryWrite==validIn) &&
                  next_state==(run ? DELAY : SAMPLE)));

// DELAY, no validIn: hold
assert property (state==DELAY && !validIn |->
                 (next_counter==counter && next_state==DELAY &&
                  !next_memoryWrite && !next_memoryLastWrite && !next_memoryRead && !next_send));

// DELAY, validIn and not at fwd terminal: write and inc
assert property (state==DELAY && validIn && (counter != {fwd,2'b11}) |->
                 (next_memoryWrite && !next_memoryLastWrite &&
                  next_counter==counter+1 && next_state==DELAY));

// DELAY, validIn and at fwd terminal: last write, go READ, reset counter
assert property (state==DELAY && validIn && (counter == {fwd,2'b11}) |->
                 (next_memoryWrite && next_memoryLastWrite &&
                  next_counter==0 && next_state==READ));

// READ: always read+send, branch on bwd terminal
assert property (state==READ && (counter == {bwd,2'b11}) |->
                 (next_memoryRead && next_send && next_counter==0 && next_state==IDLE));
assert property (state==READ && (counter != {bwd,2'b11}) |->
                 (next_memoryRead && next_send && next_counter==counter+1 && next_state==READWAIT));

// READWAIT gating
assert property (state==READWAIT && !busy && !send |-> next_state==READ);
assert property (state==READWAIT && (busy || send)   |-> next_state==READWAIT);

// ============ Sequenced behavior/invariants ============

// memoryRead/send originate only from READ and are one-cycle pulses
assert property (send      |->  memoryRead);
assert property (send      |->  $past(state)==READ);
assert property (memoryRead|->  $past(state)==READ);
assert property ($past(state)==READ |-> (send && memoryRead));
assert property (send      |-> ##1 !send);
assert property (memoryRead|-> ##1 !memoryRead);

// memoryWrite only produced from IDLE/SAMPLE/DELAY; last implies write
assert property (memoryWrite |-> ($past(state) inside {IDLE,SAMPLE,DELAY}));
assert property (memoryLastWrite |-> memoryWrite);

// Read/Write mutual exclusion
assert property (!(memoryRead && memoryWrite));

// Counter behavior across key boundaries
// From DELAY terminal -> READ with counter reset
assert property ($past(state)==DELAY && $past(validIn) &&
                 $past(counter)=={$past(fwd),2'b11} |->
                 state==READ && counter==0);

// From READ non-terminal -> READWAIT with increment
assert property ($past(state)==READ &&
                 $past(counter)!={$past(bwd),2'b11} |->
                 state==READWAIT && counter==$past(counter)+1);

// From READ terminal -> IDLE with counter reset
assert property ($past(state)==READ &&
                 $past(counter)=={$past(bwd),2'b11} |->
                 state==IDLE && counter==0);

// In IDLE/SAMPLE next counter forced to 0
assert property ($past(state) inside {IDLE,SAMPLE} |-> counter==0);

// READWAIT transition rules
assert property ($past(state)==READWAIT && $past(!busy && !send) |-> state==READ);
assert property ($past(state)==READWAIT && $past(busy || send)   |-> state==READWAIT);

// Config write semantics for fwd/bwd
assert property (wrSize |-> {fwd,bwd} == $past(config_data));
assert property (!wrSize |-> {fwd,bwd} == $past({fwd,bwd}));

// ============ Minimal but meaningful coverage ============

// Hit each state
cover property (state==IDLE);
cover property (state==SAMPLE);
cover property (state==DELAY);
cover property (state==READ);
cover property (state==READWAIT);

// Observe forward threshold event and transition to READ
cover property ($past(state)==DELAY && $past(validIn) &&
                $past(counter)=={$past(fwd),2'b11} ##1 state==READ);

// Observe read terminal back to IDLE
cover property ($past(state)==READ &&
                $past(counter)=={$past(bwd),2'b11} ##1 state==IDLE);

// Observe config write
cover property ($rose(wrSize));

`endif