// SVA for wait_generator
// Bindable checker with concise, high-value assertions and coverage

module wait_generator_sva (
  input  logic        clk,
  input  logic        nreset,
  input  logic        WAIT,
  input  logic        wait_random,
  input  logic [8:0]  wait_counter
);

  // Clocking
  default clocking cb @(posedge clk); endclocking

  // 1) Reset behavior: counter must be zero whenever reset is asserted
  // (checked in-reset; do not disable)
  assert property (@(posedge clk) !nreset |-> wait_counter == 9'h000)
    else $error("wait_counter not held at 0 during reset");

  // From here, disable assertions during reset
  default disable iff (!nreset)

  // 2) On reset release, counter should be 1 on the first active clock
  assert property ($rose(nreset) |-> wait_counter == 9'h001)
    else $error("wait_counter != 1 immediately after reset release");

  // 3) Counter increments by 1 every active cycle
  assert property (nreset && $past(nreset) |-> wait_counter == $past(wait_counter) + 9'd1)
    else $error("wait_counter failed to increment by 1");

  // 4) Combinational correctness of wait_random
  //     wait_random == WAIT && (wait_counter[5:0] != 0)
  assert property (wait_random == (WAIT && (wait_counter[5:0] != 6'h00)))
    else $error("wait_random does not match specified combinational function");

  // 5) No X/Z when active
  assert property (! $isunknown({WAIT, wait_random, wait_counter})))
    else $error("X/Z detected on active signals");

  // ----------------
  // Coverage (concise, functionally meaningful)
  // ----------------

  // Exercise both branches of wait_random logic under WAIT=1
  cover property (WAIT && (wait_counter[5:0] != 6'h00) && wait_random);
  cover property (WAIT && (wait_counter[5:0] == 6'h00) && !wait_random);

  // WAIT=0 drives wait_random low
  cover property (!WAIT && !wait_random);

  // 6-bit period observation: see two consecutive low-bit-zero events 64 cycles apart
  cover property ( (WAIT && (wait_counter[5:0] == 6'h00)) ##64 (WAIT && (wait_counter[5:0] == 6'h00)) );

  // 9-bit wrap-around
  cover property ( $past(wait_counter) == 9'h1FF && wait_counter == 9'h000 );

  // Toggle coverage for wait_random while WAIT=1
  cover property (WAIT && !wait_random ##1 WAIT && wait_random);
  cover property (WAIT &&  wait_random ##1 WAIT && !wait_random);

endmodule

// Bind into the DUT (accesses internal wait_counter)
bind wait_generator wait_generator_sva u_wait_generator_sva (
  .clk         (clk),
  .nreset      (nreset),
  .WAIT        (WAIT),
  .wait_random (wait_random),
  .wait_counter(wait_counter)
);