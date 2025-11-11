// SVA checker for four_bit_arithmetic
// Bind this file to the DUT: 
//   bind four_bit_arithmetic four_bit_arithmetic_sva sva(.A(A), .B(B), .opcode(opcode), .result(result));

module four_bit_arithmetic_sva (
  input  logic [3:0] A,
  input  logic [3:0] B,
  input  logic [1:0] opcode,
  input  logic [3:0] result
);

  // Functional correctness for all legal opcodes (inputs known)
  assert property ( (!$isunknown({A,B,opcode}) && opcode==2'b00) |=> (result == (A + B)) )
    else $error("ADD mismatch: result!=A+B");

  assert property ( (!$isunknown({A,B,opcode}) && opcode==2'b01) |=> (result == (A - B)) )
    else $error("SUB mismatch: result!=A-B");

  assert property ( (!$isunknown({A,B,opcode}) && opcode==2'b10) |=> (result == (A & B)) )
    else $error("AND mismatch: result!=A&B");

  assert property ( (!$isunknown({A,B,opcode}) && opcode==2'b11) |=> (result == (A | B)) )
    else $error("OR mismatch: result!=A|B");

  // For legal opcodes with known inputs, result must not be X/Z
  assert property ( (opcode inside {2'b00,2'b01,2'b10,2'b11}) && !$isunknown({A,B}) |=> !$isunknown(result) )
    else $error("Known inputs with legal opcode produced X/Z result");

  // If opcode has any X/Z bit, result must be all Xs (as coded in default)
  assert property ( $isunknown(opcode) |=> (result === 4'bxxxx) )
    else $error("Unknown opcode did not drive result to all Xs");

  // Basic decode coverage
  cover property ( opcode==2'b00 );
  cover property ( opcode==2'b01 );
  cover property ( opcode==2'b10 );
  cover property ( opcode==2'b11 );

  // Corner-case coverage
  // ADD overflow (carry out)
  cover property ( (opcode==2'b00) && ({1'b0,A} + {1'b0,B})[4] );

  // SUB underflow (borrow) i.e., A < B
  cover property ( (opcode==2'b01) && (A < B) );

  // AND to zero
  cover property ( (opcode==2'b10) && ((A & B) == 4'h0) );

  // OR to all ones
  cover property ( (opcode==2'b11) && ((A | B) == 4'hF) );

  // Opcode unknown coverage (drives default)
  cover property ( $isunknown(opcode) );

endmodule

// Suggested bind (place in a separate tb file or alongside this checker):
// bind four_bit_arithmetic four_bit_arithmetic_sva sva(.A(A), .B(B), .opcode(opcode), .result(result));