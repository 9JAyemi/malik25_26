// SVA for calculator
// Bind into the DUT: bind calculator calculator_sva svacal(.clk(clk), .rst(rst), .op(op), .num1(num1), .num2(num2), .result(result), .valid(valid));

module calculator_sva(
  input  logic        clk,
  input  logic        rst,
  input  logic [1:0]  op,
  input  logic [7:0]  num1,
  input  logic [7:0]  num2,
  input  logic [7:0]  result,
  input  logic        valid
);
  default clocking cb @(posedge clk); endclocking

  // Basic sanity: inputs known each cycle
  assert property (!$isunknown({rst,op,num1,num2})));

  // Synchronous reset drives outputs low in the same cycle
  assert property (rst |-> ##0 (result == 8'h00 && valid == 1'b0));

  // When not in reset, valid must be 1 in the same cycle
  assert property (!rst |-> ##0 valid);

  // Output knownness when active
  assert property (!rst |-> ##0 !$isunknown({result,valid}));

  // Arithmetic correctness (same-cycle check after NBA via ##0)
  // ADD
  assert property ((!rst && op==2'b00) |-> ##0 (result == ({1'b0,num1}+{1'b0,num2})[7:0]));
  // SUB
  assert property ((!rst && op==2'b01) |-> ##0 (result == ({1'b0,num1}-{1'b0,num2})[7:0]));
  // MUL (lower 8 bits)
  assert property ((!rst && op==2'b10) |-> ##0 (result == (num1*num2)[7:0]));
  // DIV: forbid divide-by-zero and check quotient
  assert property ((!rst && op==2'b11) |-> (num2 != 8'h00));
  assert property ((!rst && op==2'b11 && num2!=8'h00) |-> ##0 (result == (num1/num2)));

  // Valid can be 0 only if prior cycle was in reset (accounts for preponed sampling)
  assert property ((valid==1'b0) |-> $past(rst));

  // Functional coverage
  cover property (!rst && op==2'b00 |-> ##0 (result == ({1'b0,num1}+{1'b0,num2})[7:0]));
  cover property (!rst && op==2'b01 |-> ##0 (result == ({1'b0,num1}-{1'b0,num2})[7:0]));
  cover property (!rst && op==2'b10 |-> ##0 (result == (num1*num2)[7:0]));
  cover property (!rst && op==2'b11 && num2!=8'h00 |-> ##0 (result == (num1/num2)));
  // Attempted divide-by-zero seen by tests (should be prevented by assertion above)
  cover property (!rst && op==2'b11 && num2==8'h00);
  // Reset pulse and first active cycle
  cover property (rst ##1 !rst);
endmodule