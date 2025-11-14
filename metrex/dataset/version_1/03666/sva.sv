// SVA checker for rotator_shift_register
// Bind this checker to the DUT to verify rotation, shift behavior, and q mapping.

module rotator_shift_register_sva (
  input  logic         clk,
  input  logic         load,
  input  logic  [1:0]  ena,
  input  logic [99:0]  data,
  input  logic         d,
  input  logic  [2:0]  q,

  // Internal DUT regs (connected via bind)
  input  logic [99:0]  rotator_out,
  input  logic  [2:0]  shift_reg_in,
  input  logic  [2:0]  shift_reg_out
);

  default clocking cb @(posedge clk); endclocking

  // Past-valid helper (no reset in DUT)
  logic past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // Basic X checks on controls (fail if X/Z)
  assert property (cb !$isunknown({load, ena, d}))
    else $error("X/Z on control input(s)");

  // Data must be known when loaded
  assert property (cb load |-> !$isunknown(data))
    else $error("Load asserted with X/Z on data");

  // Rotator next-state behavior
  // Use 4-state equality (===) to tolerate initial unknowns due to no reset
  assert property (cb past_valid && $past(load)
                   |-> rotator_out === $past(data))
    else $error("Rotator load behavior mismatch");

  assert property (cb past_valid && !$past(load) && $past(ena[1])
                   |-> rotator_out === {$past(rotator_out)[0], $past(rotator_out)[99:1]})
    else $error("Rotator right-rotate (ena[1]) mismatch");

  assert property (cb past_valid && !$past(load) && !$past(ena[1]) && $past(ena[0])
                   |-> rotator_out === {$past(rotator_out)[98:0], $past(rotator_out)[99]})
    else $error("Rotator left-rotate (ena[0]) mismatch");

  assert property (cb past_valid && !$past(load) && !$past(ena[1]) && !$past(ena[0])
                   |-> rotator_out === $past(rotator_out))
    else $error("Rotator hold mismatch");

  // Shift-register next-state behavior
  assert property (cb past_valid
                   |-> shift_reg_in  === {$past(shift_reg_in[1:0]),  $past(d)})
    else $error("shift_reg_in shift mismatch");

  assert property (cb past_valid
                   |-> shift_reg_out === {$past(shift_reg_out[1:0]), $past(shift_reg_in[2])})
    else $error("shift_reg_out shift mismatch");

  // Functional q mapping (check when sources are known)
  assert property (cb !$isunknown({rotator_out[0],  shift_reg_out[0]})
                   |-> q[0] == (rotator_out[0]  | shift_reg_out[0]))
    else $error("q[0] OR mapping mismatch");

  assert property (cb !$isunknown({rotator_out[50], shift_reg_out[1]})
                   |-> q[1] == (rotator_out[50] | shift_reg_out[1]))
    else $error("q[1] OR mapping mismatch");

  assert property (cb !$isunknown({rotator_out[99], shift_reg_out[2]})
                   |-> q[2] == (rotator_out[99] | shift_reg_out[2]))
    else $error("q[2] OR mapping mismatch");

  // Functional coverage

  // Exercise each rotator mode and idle
  cover property (cb past_valid && $past(load));
  cover property (cb past_valid && !$past(load) && $past(ena[1]));
  cover property (cb past_valid && !$past(load) && !$past(ena[1]) && $past(ena[0]));
  cover property (cb past_valid && !$past(load) && !$past(ena[1]) && !$past(ena[0]));

  // Cover simultaneous ena bits (priority to ena[1])
  cover property (cb ena == 2'b11);

  // Show each q bit is driven high by either side of the OR (and both)
  cover property (cb rotator_out[0]  && !shift_reg_out[0] && q[0]);
  cover property (cb !rotator_out[0] &&  shift_reg_out[0] && q[0]);
  cover property (cb rotator_out[0]  &&  shift_reg_out[0] && q[0]);

  cover property (cb rotator_out[50] && !shift_reg_out[1] && q[1]);
  cover property (cb !rotator_out[50]&&  shift_reg_out[1] && q[1]);
  cover property (cb rotator_out[50] &&  shift_reg_out[1] && q[1]);

  cover property (cb rotator_out[99] && !shift_reg_out[2] && q[2]);
  cover property (cb !rotator_out[99]&&  shift_reg_out[2] && q[2]);
  cover property (cb rotator_out[99] &&  shift_reg_out[2] && q[2]);

endmodule

// Bind to DUT (connect internal regs for checking)
bind rotator_shift_register rotator_shift_register_sva u_rotator_shift_register_sva (
  .clk(clk),
  .load(load),
  .ena(ena),
  .data(data),
  .d(d),
  .q(q),
  .rotator_out(rotator_out),
  .shift_reg_in(shift_reg_in),
  .shift_reg_out(shift_reg_out)
);