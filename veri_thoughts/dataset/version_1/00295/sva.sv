// SVA bind file for top_module/alu_4bit/bitwise_or

// Assertions for ALU
module alu_4bit_sva (
  input  logic [3:0] A,
  input  logic [3:0] B,
  input  logic [2:0] opcode,
  input  logic [3:0] out,
  input  logic       zero
);
  // Functional checks per opcode
  assert property (@(A or B or opcode or out)
                   disable iff ($isunknown({A,B,opcode,out}))
                   (opcode==3'b000) |-> (out == ((A + B) & 4'hF)));

  assert property (@(A or B or opcode or out)
                   disable iff ($isunknown({A,B,opcode,out}))
                   (opcode==3'b001) |-> (out == ((A - B) & 4'hF)));

  assert property (@(A or B or opcode or out)
                   disable iff ($isunknown({A,B,opcode,out}))
                   (opcode==3'b010) |-> (out == (A & B)));

  assert property (@(A or B or opcode or out)
                   disable iff ($isunknown({A,B,opcode,out}))
                   (opcode==3'b011) |-> (out == (A | B)));

  assert property (@(A or B or opcode or out)
                   disable iff ($isunknown({A,B,opcode,out}))
                   (opcode==3'b100) |-> (out == (A ^ B)));

  // Default/unsupported opcodes
  assert property (@(A or B or opcode or out)
                   disable iff ($isunknown({A,B,opcode,out}))
                   (opcode inside {3'b101,3'b110,3'b111}) |-> (out == 4'h0));

  // Zero flag correctness
  assert property (@(out or zero)
                   disable iff ($isunknown({out,zero}))
                   zero == (out == 4'h0));

  // Opcode coverage (incl. default), zero, add overflow, sub borrow
  cover property (@(A or B or opcode) opcode==3'b000);
  cover property (@(A or B or opcode) opcode==3'b001);
  cover property (@(A or B or opcode) opcode==3'b010);
  cover property (@(A or B or opcode) opcode==3'b011);
  cover property (@(A or B or opcode) opcode==3'b100);
  cover property (@(A or B or opcode) opcode inside {3'b101,3'b110,3'b111});
  cover property (@(A or B or opcode) zero);
  cover property (@(A or B or opcode) (opcode==3'b000) && (({1'b0,A}+{1'b0,B})[4]));
  cover property (@(A or B or opcode) (opcode==3'b001) && (A < B));
endmodule

bind alu_4bit alu_4bit_sva alu_4bit_sva_i (.*);

// Assertions for bitwise_or
module bitwise_or_sva (
  input logic [3:0] A,
  input logic [3:0] B,
  input logic [3:0] out
);
  assert property (@(A or B or out)
                   disable iff ($isunknown({A,B,out}))
                   out == (A | B));
endmodule

bind bitwise_or bitwise_or_sva bitwise_or_sva_i (.*);

// Top-level integration checks
module top_module_sva (
  input logic [3:0] A,
  input logic [3:0] B,
  input logic [2:0] opcode,
  input logic [3:0] alu_out,
  input logic [3:0] out,
  input logic       zero,
  input logic [3:0] constant_value
);
  // OR stage correctness and constant enforcement
  assert property (@(alu_out or constant_value or out)
                   disable iff ($isunknown({alu_out,constant_value,out}))
                   out == (alu_out | constant_value));

  assert property (@(constant_value)
                   disable iff ($isunknown(constant_value))
                   constant_value == 4'hF);

  // Zero flag consistent with ALU output
  assert property (@(alu_out or zero)
                   disable iff ($isunknown({alu_out,zero}))
                   zero == (alu_out == 4'h0));

  // System-level coverage: each opcode seen; zero from ADD/SUB hit
  cover property (@(opcode) opcode==3'b000);
  cover property (@(opcode) opcode==3'b001);
  cover property (@(opcode) opcode==3'b010);
  cover property (@(opcode) opcode==3'b011);
  cover property (@(opcode) opcode==3'b100);
  cover property (@(opcode) opcode inside {3'b101,3'b110,3'b111});
  cover property (@(alu_out or opcode) (opcode==3'b000) && (alu_out==4'h0));
  cover property (@(alu_out or opcode) (opcode==3'b001) && (alu_out==4'h0));
endmodule

bind top_module top_module_sva top_module_sva_i (.*);