// SVA for calculator
module calculator_sva(
  input logic        clk,
  input logic        rst,
  input logic [1:0]  op,
  input logic [7:0]  a,
  input logic [7:0]  b,
  input logic [7:0]  result,
  input logic        valid
);
  default clocking cb @(posedge clk); endclocking

  // Reset behavior
  assert property (rst |-> ##1 (result==8'h00 && valid==1'b0))
    else $error("Reset did not clear outputs");

  // Valid protocol
  assert property (!rst |-> ##1 valid)
    else $error("Valid not high after non-reset cycle");

  // No unknowns during normal operation
  assert property (!rst |-> !$isunknown({result,valid}))
    else $error("Unknown on outputs");
  assert property (!rst |-> !$isunknown({op,a,b}))
    else $error("Unknown on inputs");

  // Functional correctness (1-cycle latency)
  assert property ((!rst && op==2'b00) |-> ##1 (valid && result == (a + b)))
    else $error("Addition mismatch");
  assert property ((!rst && op==2'b01) |-> ##1 (valid && result == (a - b)))
    else $error("Subtraction mismatch");
  assert property ((!rst && op==2'b10) |-> ##1 (valid && result == (a * b)[7:0]))
    else $error("Multiplication mismatch (low 8 bits)");
  assert property ((!rst && op==2'b11 && b!=8'h00) |-> ##1 (valid && result == (a / b)))
    else $error("Division mismatch");

  // Illegal operation: divide-by-zero
  assert property ((!rst && op==2'b11 && b==8'h00) |-> 1'b0)
    else $error("Divide-by-zero detected");

  // Coverage
  cover property (rst ##1 !rst ##1 valid);               // reset -> first valid
  cover property (!rst && op==2'b00 ##1 valid);          // add seen
  cover property (!rst && op==2'b01 ##1 valid);          // sub seen
  cover property (!rst && op==2'b10 ##1 valid);          // mul seen
  cover property (!rst && op==2'b11 && b!=0 ##1 valid);  // div seen

  // Edge-case coverage
  cover property (!rst && op==2'b00 && ({1'b0,a}+{1'b0,b})[8]);           // add carry-out
  cover property (!rst && op==2'b01 && (a < b));                           // sub borrow
  cover property (!rst && op==2'b10 && ((a*b)[15:8] != 8'h00));            // mul overflow (upper 8 nonzero)
  cover property (!rst && op==2'b11 && b==8'h00);                          // div-by-zero attempt
endmodule

bind calculator calculator_sva u_calculator_sva (.*);