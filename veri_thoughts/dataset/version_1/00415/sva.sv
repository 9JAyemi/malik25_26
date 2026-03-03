// SVA checker for calculator
module calculator_sva (
  input  [2:0] opcode,
  input  [7:0] A,
  input  [7:0] B,
  input  [7:0] result
);
  default clocking cb @(*); endclocking

  // Functional correctness
  assert property (opcode==3'b000 |-> result == (A + B)[7:0]);
  assert property (opcode==3'b001 |-> result == (A - B)[7:0]);
  assert property (opcode==3'b010 |-> result == (A * B)[7:0]);
  assert property ((opcode==3'b011 && B!=8'd0) |-> result == (A / B));
  assert property ((opcode==3'b011 && B==8'd0) |-> $isunknown(result));
  assert property ((opcode inside {[3'b100:3'b111]}) |-> result == 8'h00);

  // Knownness when defined
  assert property ( ((opcode inside {3'b000,3'b001,3'b010}) ||
                     (opcode==3'b011 && B!=8'd0) ||
                     (opcode inside {[3'b100:3'b111]})) |-> !$isunknown(result));

  // Pure combinational behavior (no storage)
  assert property ($stable({opcode,A,B}) |-> $stable(result));

  // Coverage: all ops, errors, and key corners
  cover property (opcode==3'b000);
  cover property (opcode==3'b001);
  cover property (opcode==3'b010);
  cover property (opcode==3'b011 && B!=8'd0);
  cover property (opcode==3'b011 && B==8'd0);
  cover property (opcode inside {[3'b100:3'b111]});
  cover property (opcode==3'b000 && (A + B) > 9'd255);     // add overflow
  cover property (opcode==3'b001 && A < B);                // subtract borrow
  cover property (opcode==3'b010 && (A * B) > 16'd255);    // multiply overflow
endmodule

// Bind into DUT
bind calculator calculator_sva u_calculator_sva (
  .opcode(opcode),
  .A(A),
  .B(B),
  .result(result)
);