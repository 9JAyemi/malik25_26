// SVA for calculator. These assert the intended functionality (result/valid reflect current a,b,op).
// Note: With the given RTL, add/sub/mul/div assertions will fail due to using temp_result in the same cycle.

module calc_sva (
  input logic        clk,
  input logic        reset,
  input logic [7:0]  a,
  input logic [7:0]  b,
  input logic [1:0]  op,
  input logic [7:0]  result,
  input logic        valid
);
  default clocking cb @(posedge clk); endclocking

  // Reset behavior
  assert property (reset |-> (result == 8'h00 && valid == 1'b0));

  // No X on outputs when inputs are 2-state
  assert property (disable iff (reset) !$isunknown({a,b,op}) |-> !$isunknown({result,valid}));

  // Valid semantics
  assert property (disable iff (reset) (op inside {2'b00,2'b01,2'b10}) |-> valid);
  assert property (disable iff (reset) (op == 2'b11 && b!=0) |-> valid);
  assert property (disable iff (reset) (op == 2'b11 && b==0) |-> (!valid && result==8'h00));

  // Functional correctness (intended spec)
  assert property (disable iff (reset) (op==2'b00) |-> (result == (a + b)[7:0]));          // add
  assert property (disable iff (reset) (op==2'b01) |-> (result == (a - b)[7:0]));          // sub
  assert property (disable iff (reset) (op==2'b10) |-> (result == (a * b)[15:8]));         // mul (upper byte)
  assert property (disable iff (reset) (op==2'b11 && b!=0) |-> (result == (a / b)[7:0]));  // div
  assert property (disable iff (reset) $isunknown(op) |-> (result == 8'h00 && !valid));    // default/X op path

  // valid is asserted iff operation is legal (post-reset)
  assert property (disable iff (reset) valid |-> ((op inside {2'b00,2'b01,2'b10}) || (op==2'b11 && b!=0)));

  // Basic operation hits
  cover property (disable iff (reset) op==2'b00);
  cover property (disable iff (reset) op==2'b01);
  cover property (disable iff (reset) op==2'b10);
  cover property (disable iff (reset) op==2'b11 && b!=0);
  cover property (disable iff (reset) op==2'b11 && b==0);

  // Corner/interesting cases
  cover property (disable iff (reset) (op==2'b00) && ((a + b) > 8'hFF));                   // add overflow
  cover property (disable iff (reset) (op==2'b00) && ((a + b) <= 8'hFF));                  // add no overflow
  cover property (disable iff (reset) (op==2'b01) && (a < b));                             // sub underflow
  cover property (disable iff (reset) (op==2'b01) && (a >= b));                            // sub no underflow
  cover property (disable iff (reset) (op==2'b10) && ((a * b)[15:8] != 8'h00));            // mul overflow to upper byte
  cover property (disable iff (reset) (op==2'b10) && ((a * b)[15:8] == 8'h00));            // mul fits in 8b
  cover property (disable iff (reset) (op==2'b11 && b!=0) && ((a % b) == 0));              // div exact
  cover property (disable iff (reset) (op==2'b11 && b!=0) && ((a % b) != 0));              // div non-zero remainder
endmodule

bind calculator calc_sva calc_sva_i (
  .clk   (clk),
  .reset (reset),
  .a     (a),
  .b     (b),
  .op    (op),
  .result(result),
  .valid (valid)
);