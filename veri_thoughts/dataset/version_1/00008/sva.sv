// SVA checker for calculator
module calculator_sva (
  input logic        clk,
  input logic [7:0]  A,
  input logic [7:0]  B,
  input logic [1:0]  op,
  input logic [7:0]  Y
);
  default clocking cb @(posedge clk); endclocking

  // Functional correctness per operation (with proper truncation)
  assert property (op==2'b00 |-> Y == (A + B));                 // add (8-bit wrap)
  assert property (op==2'b01 |-> Y == (A - B));                 // sub (8-bit wrap)
  assert property (op==2'b10 |-> Y == (A * B)[7:0]);            // mul (LSB 8)
  assert property (op==2'b11 && (B!=8'h00) |-> Y == (A / B));   // div (trunc toward 0)

  // Division-by-zero behavior: output must be unknown (X)
  assert property (op==2'b11 && (B==8'h00) |-> $isunknown(Y));

  // No X on output for all non-div-by-zero cases
  assert property ((op!=2'b11) || (B!=8'h00) |-> !$isunknown(Y));

  // Purely combinational: if inputs stable, output stable
  assert property ($stable({A,B,op}) |-> $stable(Y));

  // Functional coverage
  cover property (op==2'b00);
  cover property (op==2'b01);
  cover property (op==2'b10);
  cover property (op==2'b11);

  // Edge/overflow/exception coverage
  cover property (op==2'b00 && ({1'b0,A}+{1'b0,B})[8]);          // add overflow (carry out)
  cover property (op==2'b01 && (A < B));                          // sub borrow (underflow)
  cover property (op==2'b10 && ((A*B)[15:8] != 8'h00));           // mul overflow (upper bits nonzero)
  cover property (op==2'b11 && (B!=0) && ((A % B) == 0));         // div exact
  cover property (op==2'b11 && (B!=0) && ((A % B) != 0));         // div with remainder
  cover property (op==2'b11 && (B==0));                           // div by zero
endmodule

// Example bind (hook up an appropriate sampling clock from your environment)
// bind calculator calculator_sva u_calculator_sva (.clk(clk), .A(A), .B(B), .op(op), .Y(Y));