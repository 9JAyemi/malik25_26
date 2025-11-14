// SVA for the provided design. Bind these checkers in your sim.

// Shift register checker (binds to both shift_reg and shift_reg2)
module shift_register_sva #(parameter W=8)
(
  input logic clk,
  input logic reset,
  input logic [W-1:0] d,
  input logic [W-1:0] q
);
  default clocking cb @(posedge clk); endclocking

  // Reset drives zero
  assert property (reset |-> q == '0);

  // Shift behavior: next q is {past q[W-2:0], past d[0]}
  assert property (!reset && !$past(reset) |-> q == {$past(q[W-2:0]), $past(d[0])});

  // No X on q when not in reset
  assert property (!reset |-> !$isunknown(q));

  // Cover: observe at least one shift
  cover property (!reset ##1 q != $past(q));

  // Cover: a '1' shifted in on LSB
  cover property (!reset && d[0] ##1 q[0]);
endmodule

bind shift_register shift_register_sva #(.W(8)) u_shift_register_sva (.clk(clk), .reset(reset), .d(d), .q(q));


// Ripple-carry adder checker (uses top clock via hierarchical bind)
module ripple_carry_adder_sva
(
  input logic clk,
  input logic [3:0] a,
  input logic [3:0] b,
  input logic [3:0] sum,
  input logic       carry_out
);
  default clocking cb @(posedge clk); endclocking

  // Functional correctness with proper width (checks intended carry)
  assert property ( {carry_out,sum} == ({1'b0,a} + {1'b0,b}) );

  // Cover: carry_out asserted at least once
  cover property ( ({1'b0,a} + {1'b0,b})[4] );
endmodule

bind ripple_carry_adder ripple_carry_adder_sva u_rca_sva (.clk($root.top_module.clk), .*);


// Functional module checker (uses top clock via hierarchical bind)
module functional_module_sva
(
  input logic clk,
  input logic [7:0] shift_register_output,
  input logic [3:0] ripple_carry_adder_output,
  input logic [3:0] final_output
);
  default clocking cb @(posedge clk); endclocking

  // Exact combinational relation (4-bit truncation is inherent)
  assert property ( final_output == (shift_register_output[7:4] + ripple_carry_adder_output) );

  // Cover: overflow of the 4+4 addition (pre-truncation)
  cover property ( ({1'b0,shift_register_output[7:4]} + {1'b0,ripple_carry_adder_output})[4] );
endmodule

bind functional_module functional_module_sva u_func_sva (.clk($root.top_module.clk), .*);


// Top-level end-to-end and sanity checks
module top_module_sva
(
  input  logic        clk,
  input  logic        reset,
  input  logic [7:0]  d1,
  input  logic [7:0]  d2,
  input  logic [3:0]  adder_input,
  input  logic [7:0]  shift_register_output,
  input  logic [7:0]  shift_register_output2,
  input  logic [3:0]  ripple_carry_adder_output,
  input  logic [3:0]  final_output
);
  default clocking cb @(posedge clk); endclocking

  // No X on key IOs
  assert property (!$isunknown({d1,d2,adder_input,final_output}));

  // During reset: SR outputs zero => final_output equals adder_input
  assert property (reset |-> final_output == adder_input);

  // End-to-end functional equivalence through both blocks (4-bit truncations)
  assert property (!reset |-> final_output ==
                   ((shift_register_output[7:4] + (shift_register_output[3:0] + adder_input)[3:0]) & 4'hF));

  // Cover: top-level final_output overflow from MSBs+adder path (pre-truncation)
  cover property ( ({1'b0,shift_register_output[7:4]} + {1'b0,ripple_carry_adder_output})[4] );
endmodule

bind top_module top_module_sva u_top_sva (
  .clk(clk),
  .reset(reset),
  .d1(d1),
  .d2(d2),
  .adder_input(adder_input),
  .shift_register_output(shift_register_output),
  .shift_register_output2(shift_register_output2),
  .ripple_carry_adder_output(ripple_carry_adder_output),
  .final_output(final_output)
);