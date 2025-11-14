// SVA checker for alu. Bind this to the DUT.
module alu_sva (
  input  logic [31:0] ALUResult,
  input  logic        Zero,
  input  logic [31:0] A,
  input  logic [31:0] B,
  input  logic [2:0]  control,
  input  logic [31:0] notB,
  input  logic [31:0] muxBout,
  input  logic [31:0] S,
  input  logic [31:0] andResult,
  input  logic [31:0] orResult,
  input  logic [31:0] SLT,
  input  logic        Cout
);

  // Basic sanity (no X/Z on key controls/outputs)
  assert property (!$isunknown(control)) else $error("alu: control has X/Z");
  assert property (!$isunknown({A,B}))   else $error("alu: A/B have X/Z");
  assert property (!$isunknown({ALUResult,Zero})) else $error("alu: outputs have X/Z");

  // Internal combinational consistency
  assert property (notB    == ~B)                           else $error("alu: notB mismatch");
  assert property (muxBout == (control[2] ? notB : B))      else $error("alu: muxBout mismatch");
  assert property ({Cout,S} == ({1'b0,A} + {1'b0,muxBout} + control[2]))
                                                         else $error("alu: add/sub result mismatch");
  assert property (andResult == (A & muxBout))              else $error("alu: andResult mismatch");
  assert property (orResult  == (A | muxBout))              else $error("alu: orResult mismatch");
  assert property (SLT == {31'b0, S[31]})                   else $error("alu: SLT mismatch");

  // Output selection by control[1:0]
  assert property ((control[1:0] == 2'b00) |-> (ALUResult == andResult))
                                                         else $error("alu: AND select mismatch");
  assert property ((control[1:0] == 2'b01) |-> (ALUResult == orResult))
                                                         else $error("alu: OR select mismatch");
  assert property ((control[1:0] == 2'b10) |-> (ALUResult == S))
                                                         else $error("alu: ADD/SUB select mismatch");
  assert property ((control[1:0] == 2'b11) |-> (ALUResult == SLT))
                                                         else $error("alu: SLT select mismatch");

  // Zero flag correctness
  assert property (Zero == (ALUResult == 32'h0))            else $error("alu: Zero flag mismatch");

  // Useful covers: all 8 opcodes, Zero flag both ways, carry, negative sum, SLT=1
  cover property (control == 3'b000);
  cover property (control == 3'b001);
  cover property (control == 3'b010);
  cover property (control == 3'b011);
  cover property (control == 3'b100);
  cover property (control == 3'b101);
  cover property (control == 3'b110);
  cover property (control == 3'b111);

  cover property (Zero);
  cover property (!Zero);
  cover property (Cout);
  cover property (S[31]);
  cover property (control[1:0]==2'b11 && SLT[0]==1'b1);

  // Corner-case covers for add and sub results
  cover property (control[1:0]==2'b10 && control[2]==1'b0 && ALUResult==A+B);
  cover property (control[1:0]==2'b10 && control[2]==1'b1 && ALUResult==A + (~B) + 1'b1);

endmodule

// Bind into the DUT (accessing internal nets)
bind alu alu_sva alu_sva_i (
  .ALUResult(ALUResult),
  .Zero     (Zero),
  .A        (A),
  .B        (B),
  .control  (control),
  .notB     (notB),
  .muxBout  (muxBout),
  .S        (S),
  .andResult(andResult),
  .orResult (orResult),
  .SLT      (SLT),
  .Cout     (Cout)
);