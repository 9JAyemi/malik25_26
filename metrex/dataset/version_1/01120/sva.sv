// SVA for random_gen
// Bindable, concise, high-signal-coverage checks plus key covers

module random_gen_sva (
  input logic clk,
  input logic nreset,
  input logic WAIT,
  input logic ready_random
);
  // This module is intended to be bound into random_gen.
  // Internal signal ready_counter is referenced hierarchically.

  // Default clock for normal operation checks
  default clocking cb @(posedge clk); endclocking
  // Disable normal checks while in reset
  default disable iff (!nreset);

  // Functional correctness: counter behavior
  // Increment by 1 (mod 512) on WAIT=1
  assert property (WAIT |=> ready_counter == $past(ready_counter,1,!nreset) + 9'd1);

  // Hold value when WAIT=0
  assert property (!WAIT |=> ready_counter == $past(ready_counter,1,!nreset));

  // Any change to counter must be due to WAIT=1 (strong gating)
  assert property ($changed(ready_counter) |-> WAIT);

  // Output function correctness
  assert property (ready_random == (ready_counter[5] ^ ready_counter[4]));

  // X/Z robustness when out of reset
  assert property (nreset |-> !$isunknown(WAIT));
  assert property (!$isunknown({ready_counter, ready_random}));

  // Asynchronous reset effect observed at next clock: counter held at 0 while reset is asserted
  assert property (@(posedge clk) disable iff (1'b0)
                   (!nreset |=> ready_counter == 9'd0));

  // -----------------------------------
  // Coverage (sanity and corner cases)
  // -----------------------------------
  // See an increment after reset deassert
  cover property ($rose(nreset) ##1 WAIT ##1 $changed(ready_counter));

  // See a hold when WAIT=0
  cover property (!WAIT ##1 $stable(ready_counter));

  // See wrap-around from 9'h1FF -> 9'h000 on WAIT=1
  cover property (WAIT && $past(ready_counter,1,!nreset)==9'h1FF |=> ready_counter==9'h000);

  // ready_random takes both values and toggles
  cover property (ready_random==1'b0);
  cover property (ready_random==1'b1);
  cover property ($changed(ready_random));

endmodule

// Bind into the DUT (instantiate once per instance of random_gen)
bind random_gen random_gen_sva u_random_gen_sva (
  .clk(clk),
  .nreset(nreset),
  .WAIT(WAIT),
  .ready_random(ready_random)
);