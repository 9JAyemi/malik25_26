// SVA for Arithmetic_Unit
// Bind example (in TB): bind Arithmetic_Unit Arithmetic_Unit_sva u_sva(.clk(clk), .a(a), .b(b), .ctrl(ctrl), .result(result));

module Arithmetic_Unit_sva(
  input logic        clk,
  input logic [3:0]  a, b,
  input logic [1:0]  ctrl,
  input logic [3:0]  result
);
  default clocking cb @(posedge clk); endclocking

  // Basic sanity
  a_no_x_inputs:  assert property (!$isunknown({a,b,ctrl}));
  a_no_x_output:  assert property ((!$isunknown({a,b,ctrl})) |-> !$isunknown(result));
  a_stable_func:  assert property ($stable({a,b,ctrl}) |-> $stable(result));

  // Functional correctness
  a_add: assert property ((ctrl==2'b00) |-> (result == (a + b)));
  a_sub: assert property ((ctrl==2'b01) |-> (result == (a - b)));
  a_and: assert property ((ctrl==2'b10) |-> (result == (a & b)));
  a_or:  assert property ((ctrl==2'b11) |-> (result == (a | b)));

  // Redundant inverse check for subtraction (mod-16)
  a_sub_inverse: assert property ((ctrl==2'b01) |-> (((result + b) & 4'hF) == a));

  // Functional coverage
  c_add_seen: cover property ((ctrl==2'b00) && (result == (a + b)));
  c_sub_seen: cover property ((ctrl==2'b01) && (result == (a - b)));
  c_and_seen: cover property ((ctrl==2'b10) && (result == (a & b)));
  c_or_seen:  cover property ((ctrl==2'b11) && (result == (a | b)));

  // Corner cases
  c_add_wrap: cover property ((ctrl==2'b00) && (a==4'hF) && (b==4'h1) && (result==4'h0));
  c_sub_wrap: cover property ((ctrl==2'b01) && (a==4'h0) && (b==4'h1) && (result==4'hF));
  c_sub_zero: cover property ((ctrl==2'b01) && (a==b)     && (result==4'h0));
  c_and_zero: cover property ((ctrl==2'b10) && (a==4'hF)  && (b==4'h0) && (result==4'h0));
  c_and_all1: cover property ((ctrl==2'b10) && (a==4'hF)  && (b==4'hF) && (result==4'hF));
  c_or_pass:  cover property ((ctrl==2'b11) && (b==4'h0)  && (result==a));
  c_or_all1:  cover property ((ctrl==2'b11) && (b==4'hF)  && (result==4'hF));
endmodule