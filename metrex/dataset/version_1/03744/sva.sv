// SVA for simple_calculator
module simple_calculator_sva (
  input logic        clk,
  input logic [7:0]  a,
  input logic [7:0]  b,
  input logic [1:0]  op,
  input logic [7:0]  out
);
  default clocking cb @(posedge clk); endclocking

  // Well-formedness
  a_no_x_inputs:      assert property (!$isunknown({a,b,op}));
  out_no_x_when_known:assert property ((!$isunknown({a,b,op})) |-> !$isunknown(out));
  op_in_range:        assert property (op inside {2'b00,2'b01,2'b10,2'b11});

  // Functional correctness (combinational, same-cycle)
  add_ok: assert property (op==2'b00 |-> out == (a + b));
  sub_ok: assert property (op==2'b01 |-> out == (a - b));
  and_ok: assert property (op==2'b10 |-> out == (a & b));
  or_ok:  assert property (op==2'b11 |-> out == (a | b));

  // Combinational stability: if inputs unchanged, output unchanged
  stable_out_when_inputs_stable: assert property ($stable({a,b,op}) |-> $stable(out));

  // Functional coverage
  cover_add: cover property (op==2'b00);
  cover_sub: cover property (op==2'b01);
  cover_and: cover property (op==2'b10);
  cover_or:  cover property (op==2'b11);

  // Corner cases
  cover_add_overflow:  cover property (op==2'b00 && ((a + b) < a));
  cover_sub_underflow: cover property (op==2'b01 && (a < b));
  cover_and_zero:      cover property (op==2'b10 && ((a & b) == 8'h00));
  cover_or_full:       cover property (op==2'b11 && ((a | b) == 8'hFF));
endmodule

bind simple_calculator simple_calculator_sva sva_i (.*);