// SVA checker for logic_unit. Bind this to your DUT and provide a sampling clock/reset.

module logic_unit_sva (
  input logic        clk,
  input logic        rst_n,
  input logic [31:0] opA,
  input logic [31:0] opB,
  input logic [1:0]  op,
  input logic [31:0] result
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Basic sanity: op is never X/Z
  assert property (!$isunknown(op));

  // Functional correctness when all inputs are known
  assert property (
    !$isunknown({opA,opB,op}) |->
      result == ((op==2'b00) ? (opA & opB) :
                 (op==2'b01) ? (opA | opB) :
                 (op==2'b10) ? (opA ^ opB) :
                               ~(opA | opB))
  );

  // Optional safety: result never X/Z when inputs known
  assert property (
    !$isunknown({opA,opB,op}) |-> !$isunknown(result)
  );

  // Opcode coverage
  cover property (op == 2'b00);
  cover property (op == 2'b01);
  cover property (op == 2'b10);
  cover property (op == 2'b11);

  // Corner-case functional coverage
  cover property (op==2'b10 && opA==opB && result==32'h0000_0000);         // XOR equal -> 0
  cover property (op==2'b10 && opA==~opB && result==32'hFFFF_FFFF);         // XOR complement -> all 1s
  cover property (op==2'b00 && (opA==32'h0 || opB==32'h0) && result==32'h0);// AND with zero -> 0
  cover property (op==2'b01 && (opA==32'hFFFF_FFFF || opB==32'hFFFF_FFFF) &&
                  result==32'hFFFF_FFFF);                                   // OR with all 1s -> all 1s
  cover property (op==2'b11 && (opA|opB)==32'h0 && result==32'hFFFF_FFFF);  // NOR of zeros -> all 1s
  cover property (op==2'b11 && (opA|opB)!=32'h0 && result==32'h0000_0000);  // NOR when any 1 -> 0

endmodule

// Example bind (adjust clk/rst_n to your TB signals)
// bind logic_unit logic_unit_sva u_logic_unit_sva ( .clk(clk), .rst_n(rst_n),
//                                                   .opA(opA), .opB(opB), .op(op), .result(result) );