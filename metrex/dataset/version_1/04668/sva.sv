// SVA for calculator. Bind this module to the DUT and provide a sampling clock/reset.
module calculator_sva (
  input logic        clk,
  input logic        rst_n,
  input logic [7:0]  A,
  input logic [7:0]  B,
  input logic [1:0]  op,
  input logic [7:0]  result
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n)

  // No X/Z on inputs and consequently on result
  assert property (!$isunknown({A,B,op})) else $error("calculator: X/Z on inputs");
  assert property (!$isunknown({A,B,op}) |-> !$isunknown(result)) else $error("calculator: result X/Z with known inputs");

  // Functional correctness (same-cycle combinational behavior)
  assert property (op==2'b00 |-> result == (A+B)[7:0]) else $error("calculator add mismatch");
  assert property (op==2'b01 |-> result == (A-B)[7:0]) else $error("calculator sub mismatch");
  assert property (op==2'b10 |-> result == (A*B)[7:0]) else $error("calculator mul mismatch");
  assert property (op==2'b11 |-> B != 0) else $error("calculator div by zero");
  assert property ((op==2'b11 && B!=0) |-> result == (A/B)) else $error("calculator div mismatch");

  // Pure function: if inputs stable across a cycle, result is stable
  assert property ($stable({A,B,op}) |-> $stable(result)) else $error("calculator non-pure behavior");

  // Basic operation coverage
  cover property (op==2'b00);
  cover property (op==2'b01);
  cover property (op==2'b10);
  cover property (op==2'b11 && B!=0);

  // Interesting edge-case coverage
  cover property (op==2'b11 && B==0);                                   // div-by-zero attempted
  cover property (op==2'b00 && ({1'b0,A}+{1'b0,B})[8]);                 // add overflow
  cover property (op==2'b01 && (A < B));                                // sub borrow
  cover property (op==2'b10 && ((A*B) > 8'hFF));                        // mul overflow/truncation
  cover property (op==2'b11 && B==1);                                   // divide by 1
  cover property (op==2'b11 && B!=0 && (A < B));                        // div quotient=0

endmodule

// Example bind (adjust clk/rst paths to your environment):
// bind calculator calculator_sva u_calculator_sva ( .clk(tb_clk), .rst_n(tb_rst_n), .A(A), .B(B), .op(op), .result(result) );