// SVA for Problem3
// Bind with: bind Problem3 Problem3_sva sva_i(.*);

module Problem3_sva (
  input  logic [2:0] OpCode,
  input  logic [3:0] A,
  input  logic [3:0] B,
  input  logic [3:0] Final,
  input  logic       Status
);

  // Helper: known inputs
  function automatic bit known_inputs();
    return !$isunknown({OpCode,A,B});
  endfunction

  // Outputs must be known when inputs are known
  assert property (@(*) known_inputs() |-> !$isunknown({Final,Status}));

  // Opcode 000: NOT A
  assert property (@(*) known_inputs() && (OpCode==3'b000) |-> (Final === ~A && Status === 1'b0));

  // Opcode 001: NAND
  assert property (@(*) known_inputs() && (OpCode==3'b001) |-> (Final === ~(A & B) && Status === 1'b0));

  // Opcode 010: NOR
  assert property (@(*) known_inputs() && (OpCode==3'b010) |-> (Final === ~(A | B) && Status === 1'b0));

  // Opcode 011: XOR
  assert property (@(*) known_inputs() && (OpCode==3'b011) |-> (Final === (A ^ B) && Status === 1'b0));

  // Opcode 100: ADD with signed overflow flag
  assert property (@(*) known_inputs() && (OpCode==3'b100) |-> (
      Final  === (A + B) &&
      Status === ((A[3]==B[3]) && (((A+B)[3]) != B[3]))
  ));

  // Opcode 101: SUB with signed overflow flag
  assert property (@(*) known_inputs() && (OpCode==3'b101) |-> (
      Final  === (A - B) &&
      Status === ((A[3]!=B[3]) && (((A-B)[3]) != A[3]))
  ));

  // Opcode 110: INC(B) with signed overflow flag
  assert property (@(*) known_inputs() && (OpCode==3'b110) |-> (
      Final  === (B + 4'b0001) &&
      Status === ((B[3]==1'b0) && (((B+4'b0001)[3]) != B[3]))
  ));

  // Opcode 111: DEC(B) with signed overflow flag
  assert property (@(*) known_inputs() && (OpCode==3'b111) |-> (
      Final  === (B - 4'b0001) &&
      Status === ((B[3]==1'b1) && (((B-4'b0001)[3]) != 1'b1))
  ));

  // Status must only be 1 on valid arithmetic overflow conditions
  assert property (@(*) known_inputs() && (Status===1'b1) |->
      ((OpCode==3'b100 && (A[3]==B[3]) && (((A+B)[3]) != B[3])) ||
       (OpCode==3'b101 && (A[3]!=B[3]) && (((A-B)[3]) != A[3])) ||
       (OpCode==3'b110 && (B[3]==1'b0) && (((B+4'b0001)[3]) != B[3])) ||
       (OpCode==3'b111 && (B[3]==1'b1) && (((B-4'b0001)[3]) != 1'b1)))
  );

  // Basic functional coverage
  cover property (@(*) !$isunknown(OpCode) && OpCode==3'b000);
  cover property (@(*) !$isunknown(OpCode) && OpCode==3'b001);
  cover property (@(*) !$isunknown(OpCode) && OpCode==3'b010);
  cover property (@(*) !$isunknown(OpCode) && OpCode==3'b011);
  cover property (@(*) !$isunknown(OpCode) && OpCode==3'b100);
  cover property (@(*) !$isunknown(OpCode) && OpCode==3'b101);
  cover property (@(*) !$isunknown(OpCode) && OpCode==3'b110);
  cover property (@(*) !$isunknown(OpCode) && OpCode==3'b111);

  // Overflow scenario coverage
  cover property (@(*) known_inputs() && OpCode==3'b100 && (A[3]==B[3]) && (((A+B)[3]) != B[3]) && Status);
  cover property (@(*) known_inputs() && OpCode==3'b101 && (A[3]!=B[3]) && (((A-B)[3]) != A[3]) && Status);
  cover property (@(*) known_inputs() && OpCode==3'b110 && (B[3]==1'b0) && (((B+4'b0001)[3]) != B[3]) && Status);
  cover property (@(*) known_inputs() && OpCode==3'b111 && (B[3]==1'b1) && (((B-4'b0001)[3]) != 1'b1) && Status);

endmodule