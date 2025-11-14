// SVA bind file for the provided design

// Barrel shifter checks
module barrel_shifter_sva (input logic [15:0] in, input logic [7:0] out);
  default clocking cb @ (posedge $global_clock); endclocking

  // Functional correctness
  a_bs_func:  assert property (out === in[7:0]);
  // No-X on output when input known
  a_bs_no_x:  assert property (!$isunknown(in) |-> !$isunknown(out));
  // Simple activity coverage
  c_bs_chg:   cover  property ($changed(in));
endmodule
bind barrel_shifter barrel_shifter_sva(.in(in), .out(out));


// Mux checks
module mux_2to1_sva (input logic [7:0] in0, in1, input logic ctrl, input logic [7:0] out);
  default clocking cb @ (posedge $global_clock); endclocking

  // Functional correctness
  a_mux_func: assert property (out === (ctrl ? in1 : in0));
  // No-X on output when inputs known
  a_mux_no_x: assert property (!$isunknown({in0,in1,ctrl}) |-> !$isunknown(out));
  // Coverage: both selections and toggle
  c_sel0:     cover  property (!ctrl);
  c_sel1:     cover  property ( ctrl);
  c_rose:     cover  property ($rose(ctrl));
  c_fell:     cover  property ($fell(ctrl));
endmodule
bind mux_2to1 mux_2to1_sva(.in0(in0), .in1(in1), .ctrl(ctrl), .out(out));


// Bitwise OR checks
module bitwise_or_sva (input logic [7:0] in0, in1, input logic [7:0] out);
  default clocking cb @ (posedge $global_clock); endclocking

  // Functional correctness
  a_or_func:  assert property (out === (in0 | in1));
  // No-X on output when inputs known
  a_or_no_x:  assert property (!$isunknown({in0,in1}) |-> !$isunknown(out));
  // Corner coverage
  c_or_zero:  cover  property (out == 8'h00);
  c_or_ones:  cover  property (out == 8'hFF);
  c_or_in0:   cover  property ((in1 == 8'h00) && (out == in0));
  c_or_in1:   cover  property ((in0 == 8'h00) && (out == in1));
endmodule
bind bitwise_or bitwise_or_sva(.in0(in0), .in1(in1), .out(out));


// Top-level composition checks
module top_module_sva (
  input  logic [15:0] in,
  input  logic        ctrl,
  input  logic [7:0]  out,
  input  logic [7:0]  out_or,
  // tap internals
  input  logic [7:0]  upper_out,
  input  logic [7:0]  lower_out
);
  default clocking cb @ (posedge $global_clock); endclocking

  // Barrel shifter instance effects
  a_low_func:  assert property (lower_out === in[7:0]);
  a_up_func:   assert property (upper_out === in[15:8]);

  // Mux/OR top-level behavior
  a_top_out:   assert property (out    === (ctrl ? in[15:8] : in[7:0]));
  a_top_or:    assert property (out_or === (in[15:8] | in[7:0]));
  // Consistency between mux and OR paths
  a_consist:   assert property (out_or === (out | (ctrl ? lower_out : upper_out)));

  // Stability: if inputs stable, outputs stable
  a_stable:    assert property ($stable({in,ctrl}) |-> $stable({out,out_or,upper_out,lower_out}));

  // Coverage: exercise both halves and selections
  c_halves_diff: cover property (in[15:8] != in[7:0]);
  c_sel0_diff:   cover property ((!ctrl) && (in[15:8] != in[7:0]));
  c_sel1_diff:   cover property (( ctrl) && (in[15:8] != in[7:0]));
  c_or_zero:     cover property (out_or == 8'h00);
  c_or_ones:     cover property (out_or == 8'hFF);
endmodule
bind top_module top_module_sva(
  .in(in), .ctrl(ctrl), .out(out), .out_or(out_or),
  .upper_out(upper_out), .lower_out(lower_out)
);