// SVA for alu. Bind this module to the DUT.
// Focus: cycle-accurate functional correctness, X-propagation, and concise coverage.

module alu_sva (
  input logic        clk,
  input logic [3:0]  A,
  input logic [3:0]  B,
  input logic [2:0]  op,
  input logic [3:0]  result,
  input logic        valid
);

  default clocking cb @(posedge clk); endclocking

  // Golden model for 4-bit result behavior
  function automatic logic [3:0] model (logic [2:0] op_i, logic [3:0] a_i, logic [3:0] b_i);
    case (op_i)
      3'b000: model = a_i + b_i;   // add (wraps to 4b)
      3'b001: model = a_i - b_i;   // sub (wraps to 4b)
      3'b010: model = a_i & b_i;
      3'b011: model = a_i | b_i;
      3'b100: model = a_i ^ b_i;
      default: model = 4'h0;
    endcase
  endfunction

  // Valid should be asserted every cycle (no reset in DUT; first sampled cycle is already 1)
  assert property (valid)
    else $error("valid must be 1 every cycle");

  // Functional correctness: result equals model(op, $past(A), $past(B))
  // Guard against first-cycle/unknowns using !$isunknown on past operands and op.
  assert property ( !$isunknown({op, $past(A), $past(B)}) |-> (result == model(op, $past(A), $past(B))) )
    else $error("ALU result mismatch");

  // Invalid op codes must yield zero
  assert property ( (op inside {3'b101,3'b110,3'b111}) |-> (result == 4'h0) )
    else $error("Invalid op must produce 0");

  // No X on result when inputs (past A/B) and op are known
  assert property ( !$isunknown({op, $past(A), $past(B)}) |-> !$isunknown(result) )
    else $error("X on result with known inputs/op");

  // Basic functional coverage
  cover property ( op == 3'b000 ); // add
  cover property ( op == 3'b001 ); // sub
  cover property ( op == 3'b010 ); // and
  cover property ( op == 3'b011 ); // or
  cover property ( op == 3'b100 ); // xor
  cover property ( op inside {3'b101,3'b110,3'b111} && result == 4'h0 ); // default case hit

  // Corner-case coverage
  cover property ( !$isunknown({$past(A),$past(B)}) && op==3'b000 && (($past(A)+$past(B)) > 4'hF) ); // add overflow
  cover property ( !$isunknown({$past(A),$past(B)}) && op==3'b001 && ($past(A) < $past(B)) );        // sub underflow
  cover property ( !$isunknown({$past(A),$past(B)}) && op==3'b100 && ($past(A) == $past(B)) && result==4'h0 ); // xor self=0
  cover property ( $changed(op) && $changed({A,B}) ); // exercise op/operand skew vs pipeline

endmodule

// Example bind (in a testbench or separate bind file):
// bind alu alu_sva alu_sva_i (.clk(clk), .A(A), .B(B), .op(op), .result(result), .valid(valid));