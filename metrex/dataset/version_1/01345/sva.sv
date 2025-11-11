// SVA for calculator
module calculator_sva(
  input logic [7:0] a,
  input logic [7:0] b,
  input logic [1:0] op,
  input logic       start,
  input logic       done,
  input logic [7:0] result
);

  default clocking cb @(posedge start); endclocking

  // Basic sanity
  assert property (!$isunknown({a,b,op}));
  assert property (##0 !$isunknown({result,done}));

  // done behavior as implemented (always ends low after operation)
  assert property (##0 done == 1'b0);

  // Arithmetic correctness (8-bit wrap semantics)
  assert property ((op == 2'b00) |-> ##0 (result == (a + b)[7:0]));
  assert property ((op == 2'b01) |-> ##0 (result == (a - b)[7:0]));
  assert property ((op == 2'b10) |-> ##0 (result == (a * b)[7:0]));

  // Division special cases / default arm behavior
  assert property ((op == 2'b11 && b == 8'd0) |-> ##0 (result == 8'hFF));
  assert property ((op == 2'b11 && b != 8'd0) |-> ##0 (done == 1'b0));
  assert property ($isunknown(op) |-> ##0 (result == 8'hFF));

  // Functional coverage
  cover property (op == 2'b00);
  cover property (op == 2'b01);
  cover property (op == 2'b10);
  cover property (op == 2'b11);
  cover property (op == 2'b11 && b == 8'd0);                 // div by zero
  cover property (op == 2'b10 && ((a*b) >> 8) != 0);         // mul overflow
  cover property (op == 2'b00 && (a + b) > 8'hFF);           // add overflow
  cover property (op == 2'b01 && (a < b));                   // sub underflow

endmodule

bind calculator calculator_sva sva_i(
  .a(a), .b(b), .op(op), .start(start), .done(done), .result(result)
);