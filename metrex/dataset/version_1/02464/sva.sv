// SVA for calculator. Bind this module to the DUT.
module calculator_sva #(parameter int W=8)
(
  input  logic              clk,
  input  logic              reset,
  input  logic [W-1:0]      a,
  input  logic [W-1:0]      b,
  input  logic [1:0]        opcode,
  input  logic [W-1:0]      result
);

  default clocking cb @(posedge clk); endclocking

  // Reset behavior
  a_reset_zero: assert property (reset |-> ##0 (result == '0));

  // Functional correctness per opcode (synchronous result)
  a_add: assert property (disable iff (reset) (opcode == 2'b00) |-> ##0 (result == a + b));
  a_sub: assert property (disable iff (reset) (opcode == 2'b01) |-> ##0 (result == a - b));
  a_mul: assert property (disable iff (reset) (opcode == 2'b10) |-> ##0 (result == a * b));

  // Division: handle non-zero and zero divisors explicitly
  a_div_nz:  assert property (disable iff (reset) (opcode == 2'b11 && b != '0) |-> ##0 (result == a / b));
  a_div_z_x: assert property (disable iff (reset) (opcode == 2'b11 && b == '0) |-> ##0 $isunknown(result));

  // No X on result when inputs are known and no div-by-zero
  a_no_x: assert property (
    disable iff (reset)
    (!$isunknown({a,b,opcode}) && !(opcode==2'b11 && b=='0)) |-> ##0 !$isunknown(result)
  );

  // Stability: if inputs/opcode stable across cycles (and not in/just after reset), result must be stable
  a_stable: assert property (
    disable iff (reset)
    ($past(!reset) && $stable({a,b,opcode})) |-> ##0 $stable(result)
  );

  // Coverage: reset, each opcode, and key corner cases
  c_reset_release: cover property (reset ##1 !reset);

  c_op_add: cover property (disable iff (reset) (opcode == 2'b00));
  c_op_sub: cover property (disable iff (reset) (opcode == 2'b01));
  c_op_mul: cover property (disable iff (reset) (opcode == 2'b10));
  c_op_div: cover property (disable iff (reset) (opcode == 2'b11));

  // Add overflow (carry out)
  c_add_overflow: cover property (disable iff (reset)
    (opcode == 2'b00) && ({1'b0,a} + {1'b0,b})[W]
  );

  // Sub borrow (a < b)
  c_sub_borrow: cover property (disable iff (reset)
    (opcode == 2'b01) && (a < b)
  );

  // Mul overflow: upper bits of extended product non-zero
  c_mul_overflow: cover property (disable iff (reset)
    (opcode == 2'b10) &&
    ( ( {{W{1'b0}},a} * {{W{1'b0}},b} )[2*W-1:W] != '0 )
  );

  // Division by zero and non-zero pathways
  c_div_by_zero:  cover property (disable iff (reset) (opcode == 2'b11) && (b == '0));
  c_div_non_zero: cover property (disable iff (reset) (opcode == 2'b11) && (b != '0));

endmodule

// Bind to DUT
bind calculator calculator_sva #(.W(8)) calculator_sva_b (.*);