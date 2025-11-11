// SVA for calculator
module calculator_sva (
  input logic        clk,
  input logic        rst,
  input logic [1:0]  op,
  input logic [31:0] a,
  input logic [31:0] b,
  input logic [31:0] result
);
  default clocking cb @(posedge clk); endclocking

  // Sanity: no X/Z on controls and data when not in reset
  assert property (!rst |-> !$isunknown({op,a,b})) else $error("X/Z on inputs when not in reset");

  // Reset behavior
  assert property (rst |=> result == 32'd0) else $error("Result not cleared after reset");
  assert property (rst && $past(rst) |-> result == 32'd0) else $error("Result not held at 0 during sustained reset");

  // Functional correctness (uses previous-cycle inputs, synchronous update)
  assert property (!rst && $past(!rst) && $past(op)==2'b00 |-> result == $past(a)+$past(b))
    else $error("ADD mismatch");
  assert property (!rst && $past(!rst) && $past(op)==2'b01 |-> result == $past(a)-$past(b))
    else $error("SUB mismatch");
  assert property (!rst && $past(!rst) && $past(op)==2'b10 |-> result == $past(a)*$past(b))
    else $error("MUL mismatch");
  // Divide by non-zero
  assert property (!rst && $past(!rst) && $past(op)==2'b11 && $past(b)!=0 |-> result == ($past(a) / $past(b)))
    else $error("DIV mismatch");
  // Divide-by-zero yields unknown (as per Verilog semantics)
  assert property (!rst && $past(!rst) && $past(op)==2'b11 && $past(b)==0 |-> $isunknown(result))
    else $error("DIV by zero did not produce X");

  // Result known on all non-reset, non-div0 operations
  assert property (!rst && $past(!rst) &&
                   ($past(op)!=2'b11 || $past(b)!=0) |-> !$isunknown(result))
    else $error("Result unknown on valid operation");

  // Stability: if inputs/op are stable across cycles (and not in reset), result is stable
  assert property (!rst && $past(!rst) &&
                   op==$past(op) && a==$past(a) && b==$past(b) |-> result==$past(result))
    else $error("Result changed despite stable inputs/op");

  // Coverage
  cover property (rst ##1 !rst);                       // reset deassertion
  cover property (!rst && op==2'b00);                  // add op seen
  cover property (!rst && op==2'b01);                  // sub op seen
  cover property (!rst && op==2'b10);                  // mul op seen
  cover property (!rst && op==2'b11 && b!=0);          // div op seen (legal)
  cover property (!rst && op==2'b11 && b==0);          // div-by-zero attempted
endmodule

// Bind into DUT (example)
// bind calculator calculator_sva i_calculator_sva (.*)