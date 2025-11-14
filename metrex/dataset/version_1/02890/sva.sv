// SVA for top_module and submodules. Bind these checkers to the DUT.

`default_nettype none
timeunit 1ns; timeprecision 1ps;

// transition_detector assertions
module td_sva #(parameter WIDTH=32)(
  input logic                 clk,
  input logic                 reset,
  input logic [WIDTH-1:0]     in,
  input logic [WIDTH-1:0]     out
);
  default clocking cb @(posedge clk); endclocking

  // Functional relation: out flags 1->0 transitions of in
  a_td_func: assert property (disable iff (reset) out == ($past(in) & ~in));

  // Known and reset behavior
  a_td_zero_on_reset: assert property (reset |-> out == '0);
  a_td_known:         assert property (!$isunknown(out));

  // Coverage: detect any transition
  c_td_transition:    cover property (disable iff (reset) (($past(in) & ~in) != '0));
endmodule
bind transition_detector td_sva td_sva_i(.clk(clk), .reset(reset), .in(in), .out(out));

// bcd_counter assertions
module bc_sva(
  input logic         clk,
  input logic         reset,
  input logic         ena,
  input logic [15:0]  out
);
  default clocking cb @(posedge clk); endclocking

  // Reset drives zero
  a_bc_reset:              assert property (reset |-> out == 16'h0000);

  // Hold when disabled
  a_bc_hold_when_disabled: assert property (disable iff (reset) !ena |=> out == $past(out));

  // Increment when enabled (not at terminal value)
  a_bc_inc:                assert property (disable iff (reset) (ena && $past(out) != 16'h9999) |=> out == $past(out) + 16'h0001);

  // Wrap at 9999
  a_bc_wrap:               assert property (disable iff (reset) (ena && $past(out) == 16'h9999) |=> out == 16'h0000);

  // BCD digit validity (detects non-BCD counting)
  a_bc_bcd_digits:         assert property (disable iff (reset)
                                   (out[3:0] <= 9 && out[7:4] <= 9 && out[11:8] <= 9 && out[15:12] <= 9));

  a_bc_known:              assert property (!$isunknown(out));

  // Coverage
  c_bc_inc:                cover property (disable iff (reset) (ena && $past(out) != 16'h9999) |=> out == $past(out) + 16'h1);
  c_bc_wrap:               cover property (disable iff (reset) (ena && $past(out) == 16'h9999) |=> out == 16'h0000);
endmodule
bind bcd_counter bc_sva bc_sva_i(.clk(clk), .reset(reset), .ena(ena), .out(out));

// max_value_selector assertions (combinational)
module mvs_chk(
  input  logic [31:0] in1,
  input  logic [15:0] in2,
  input  logic [15:0] out
);
  // Immediate assertions for combinational equivalence and knownness
  always_comb begin
    assert (!$isunknown({in1,in2,out})) else $error("mvs: X/Z detected");
    assert (out == ((in1 > {16'h0,in2}) ? in1[15:0] : in2))
      else $error("mvs: selection mismatch");
    // Coverage for both selection paths (procedural cover)
    cover (in1 > {16'h0,in2});
    cover (!(in1 > {16'h0,in2}));
    cover (in1 == {16'h0,in2}); // equal case selects in2
  end
endmodule
bind max_value_selector mvs_chk mvs_chk_i(.in1(in1), .in2(in2), .out(out));

// top_module integration assertions
module top_sva(
  input  logic         clk,
  input  logic         reset,
  input  logic [31:0]  in,
  input  logic [15:0]  q,
  input  logic [3:0]   ena,
  input  logic [31:0]  transition_detected,
  input  logic [15:0]  bcd_counter
);
  default clocking cb @(posedge clk); endclocking

  // ena is tied off
  a_ena_const: assert property (ena == 4'b0000);

  // With ena==0, counter must hold after reset deasserts
  a_bc_stable_due_to_ena0: assert property (disable iff (reset) 1'b1 |=> bcd_counter == $past(bcd_counter));

  // q equals max_value_selector function
  a_q_function: assert property (
    q == ((transition_detected > {16'h0,bcd_counter}) ? transition_detected[15:0] : bcd_counter)
  );

  a_q_known:    assert property (!$isunknown(q));

  // Coverage: both selector paths and reset seen
  c_sel_in1:    cover property (transition_detected > {16'h0,bcd_counter});
  c_sel_in2:    cover property (!(transition_detected > {16'h0,bcd_counter}));
  c_reset_ev:   cover property ($rose(reset));
endmodule
bind top_module top_sva top_sva_i(.*);

`default_nettype wire