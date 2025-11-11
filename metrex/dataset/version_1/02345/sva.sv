// SVA checker for top_module
// Bind example (provide a clock/reset in your env):
// bind top_module top_module_sva u_top_module_sva(.clk(clk), .rst_n(rst_n), .*);

module top_module_sva (
  input logic clk, rst_n,
  input logic [31:0] A, B,
  input logic [3:0]  S,
  input logic [2:0]  OPCODE,
  input logic        CIN,
  input logic        COUT,
  input logic [31:0] Y
);

  default clocking @(posedge clk); endclocking
  default disable iff (!rst_n)

  let sum33  = {1'b0, A} + {1'b0, B} + CIN;
  let diff33 = {1'b0, A} - {1'b0, B} - {32'b0, ~CIN};
  let shamt  = S[3:1];

  // Functional correctness
  assert property (OPCODE == 3'b000 |-> (Y === sum33[31:0]  && COUT === sum33[32]));
  assert property (OPCODE == 3'b001 |-> (Y === diff33[31:0] && COUT === ~diff33[32]));

  assert property (OPCODE == 3'b010 |-> (Y === (A & B) && COUT === 1'b0));
  assert property (OPCODE == 3'b011 |-> (Y === (A | B) && COUT === 1'b0));
  assert property (OPCODE == 3'b100 |-> (Y === (A ^ B) && COUT === 1'b0));

  assert property (OPCODE == 3'b101 |-> (
      Y    === ((S == 0) ? A : (A << shamt)) &&
      COUT === ((S != 0) ? B[32 - shamt] : B[shamt - 1])
  ));

  assert property (OPCODE == 3'b110 |-> (
      Y    === ((S == 0) ? B : (B << shamt)) &&
      COUT === ((S != 0) ? B[32 - shamt] : B[shamt - 1])
  ));

  assert property (OPCODE == 3'b111 |-> (Y === 32'b0 && COUT === 1'b0));

  // Guard checks for known out-of-range bit-select cases in the RTL COUT expression for shift ops
  assert property ((OPCODE inside {3'b101,3'b110}) && (S == 0)         |-> $isunknown(COUT));
  assert property ((OPCODE inside {3'b101,3'b110}) && (S != 0) && (shamt == 0) |-> $isunknown(COUT));

  // Minimal negative checks
  assert property ((OPCODE inside {3'b010,3'b011,3'b100}) |-> COUT === 1'b0);

  // Coverage
  cover property (OPCODE == 3'b000);
  cover property (OPCODE == 3'b001);
  cover property (OPCODE == 3'b010);
  cover property (OPCODE == 3'b011);
  cover property (OPCODE == 3'b100);
  cover property (OPCODE == 3'b101);
  cover property (OPCODE == 3'b110);
  cover property (OPCODE == 3'b111);

  cover property (OPCODE == 3'b000 && COUT == 1'b1);
  cover property (OPCODE == 3'b000 && COUT == 1'b0);

  cover property (OPCODE == 3'b001 && COUT == 1'b1);
  cover property (OPCODE == 3'b001 && COUT == 1'b0);

  cover property (OPCODE == 3'b101 && S == 0);
  cover property (OPCODE == 3'b101 && S != 0);
  cover property (OPCODE == 3'b110 && S == 0);
  cover property (OPCODE == 3'b110 && S != 0);

endmodule