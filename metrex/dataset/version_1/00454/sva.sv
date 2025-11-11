// SVA for calculator — bind to DUT, uses $global_clock for combinational sampling
module calculator_sva(
  input logic [31:0] a,
  input logic [31:0] b,
  input logic [1:0]  op,
  input logic [31:0] c
);
  default clocking cb @(posedge $global_clock); endclocking

  // Basic sanity
  ap_op_known:    assert property (!$isunknown(op));
  ap_io_known:    assert property (!$isunknown({a,b})) else $warning("X/Z on inputs may corrupt result");
  ap_c_known:     assert property (!(op==2'b11 && b==0) |-> !$isunknown(c));

  // Functional correctness
  ap_add:         assert property (op==2'b00 |-> c == (a + b));
  ap_sub:         assert property (op==2'b01 |-> c == (a - b));
  ap_mul:         assert property (op==2'b10 |-> c == (a * b)[31:0]);
  ap_div_no_z:    assert property (op==2'b11 |-> b != 0);
  ap_div_val:     assert property (op==2'b11 && b!=0 |-> c == (a / b));

  // Full op space covered (also catches X/Z on op)
  ap_op_legal:    assert property (op inside {2'b00,2'b01,2'b10,2'b11});

  // Coverage
  cv_add:         cover  property (op==2'b00 && c == (a + b));
  cv_sub:         cover  property (op==2'b01 && c == (a - b));
  cv_mul:         cover  property (op==2'b10 && c == (a * b)[31:0]);
  cv_div:         cover  property (op==2'b11 && b!=0 && c == (a / b));
  cv_div_by_zero: cover  property (op==2'b11 && b==0);
  cv_mul_ovf:     cover  property (op==2'b10 && (a*b)[63:32] != 0);
  cv_add_wrap:    cover  property (op==2'b00 && (a + b) < a);
  cv_sub_wrap:    cover  property (op==2'b01 && a < b);
endmodule

bind calculator calculator_sva sva_calculator (.*);