// SVA checker for alu_4bit
module alu_4bit_sva (
  input logic [3:0] A,
  input logic [3:0] B,
  input logic [2:0] OP,
  input logic [3:0] result
);

  // Sample on any change of inputs/outputs (combinational)
  default clocking cb @(A or B or OP or result); endclocking

  // Functional correctness for each defined opcode
  assert property ( (OP==3'b000) |-> ##0 (result == ((A + B) & 4'hF)) ) else $error("ADD mismatch");
  assert property ( (OP==3'b001) |-> ##0 (result == ((A - B) & 4'hF)) ) else $error("SUB mismatch");
  assert property ( (OP==3'b010) |-> ##0 (result == (A & B)) )        else $error("AND mismatch");
  assert property ( (OP==3'b011) |-> ##0 (result == (A | B)) )        else $error("OR mismatch");
  assert property ( (OP==3'b100) |-> ##0 (result == (A ^ B)) )        else $error("XOR mismatch");
  assert property ( (OP==3'b101) |-> ##0 (result == ((A << 1) & 4'hF)) ) else $error("SHL mismatch");

  // Defined opcodes must not produce X/Z; invalid opcodes must produce all X
  assert property ( (OP inside {[3'b000:3'b101]}) |-> ##0 !$isunknown(result) ) else $error("Unexpected X/Z on defined OP");
  assert property ( (OP inside {3'b110,3'b111}) |-> ##0 (result === 4'bxxxx) )  else $error("Invalid OP must drive Xs");

  // Cross-check bit-level behavior for shift (MSB drop, LSB zero)
  assert property ( (OP==3'b101) |-> ##0 (result[0]==1'b0 && result[3]==A[2]) ) else $error("Shift-left bit behavior mismatch");

  // Basic one-hot decode consistency (no overlap among defined cases)
  assert property ( (OP inside {[3'b000:3'b101]}) or (OP inside {3'b110,3'b111}) );

  // Coverage: opcodes and corner cases
  cover property (OP==3'b000);
  cover property (OP==3'b001);
  cover property (OP==3'b010);
  cover property (OP==3'b011);
  cover property (OP==3'b100);
  cover property (OP==3'b101);
  cover property (OP inside {3'b110,3'b111} && result === 4'bxxxx);

  // Coverage: add overflow and sub underflow, shift MSB drop
  cover property ((OP==3'b000) && (({1'b0,A}+{1'b0,B}) > 5'h0F));
  cover property ((OP==3'b001) && ($unsigned(A) < $unsigned(B)));
  cover property ((OP==3'b101) && A[3]==1'b1);

endmodule

// Bind into the DUT
bind alu_4bit alu_4bit_sva i_alu_4bit_sva (.A(A), .B(B), .OP(OP), .result(result));