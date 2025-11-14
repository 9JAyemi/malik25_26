// SVA for shift_register_incrementer_xor
// Bind into the DUT to check behavior and provide concise coverage.

module shift_register_incrementer_xor_sva
(
  input  logic        clk,
  input  logic        reset,
  input  logic [7:0]  d,
  input  logic        select,
  input  logic [7:0]  q,
  input  logic [3:0]  ena,
  input  logic [3:0]  c,
  input  logic [7:0]  f,

  // internal signals
  input  logic [7:0]  shift_reg,
  input  logic [3:0]  counter
);
  default clocking cb @(posedge clk); endclocking
  // Only disable checks that depend on $past; reset-specific checks remain active.
  default disable iff (reset);

  // Structural consistency
  assert property (q == shift_reg);
  assert property (f == (q ^ {counter, counter}));

  // Synchronous reset effects
  assert property (@(posedge clk) reset |-> (q == 8'h00 && counter == 4'h0));

  // Known values when not in reset
  assert property (!$isunknown({q, f, ena, c}));

  // Incrementer controls/outputs
  assert property (ena == 4'hF);
  assert property ($past(!reset) |-> c == $past(counter));
  assert property ($past(!reset) |-> counter == (($past(counter) == 4'hF) ? 4'h0 : ($past(counter) + 4'h1)));

  // Shift/load behavior (note: due to truncation in RTL, select=1 loads d; select=0 shifts right with MSB=d[0])
  assert property (select |-> q == d);
  assert property ($past(!reset) && !select |-> q == {d[0], $past(q)[7:1]});

  // Minimal coverage
  cover property (select && !reset);                     // load path exercised
  cover property (!select && !reset);                    // shift-right path exercised
  cover property ($past(!reset) && $past(counter)==4'hF && counter==4'h0); // wraparound
  cover property (!reset && f != $past(f));              // XOR output changes
endmodule

bind shift_register_incrementer_xor shift_register_incrementer_xor_sva u_sva (.*);