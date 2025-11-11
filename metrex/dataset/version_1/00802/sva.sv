// SVA bind module for MyTruthComplement
module MyTruthComplement_sva(
  input  logic [5:0] yIn,
  input  logic [5:0] yOut,
  input  logic [5:0] inverted_yIn
);
  default clocking cb @(*); endclocking

  // Expected combinational behavior
  let exp = yIn[5] ? ({1'b1, ~yIn[4:0]} + 6'b000001) : yIn;

  // Functional equivalence to spec
  assert property (cb yOut == exp);

  // Internal net correctness
  assert property (cb inverted_yIn == ~yIn);

  // Branch-specific checks
  assert property (cb !yIn[5] |-> (yOut == yIn));
  assert property (cb yIn[5]  |-> (yOut[4:0] == (~yIn[4:0] + 5'b00001)));

  // Sign-bit behavior (including special case)
  assert property (cb (!yIn[5]) |-> (yOut[5] == 1'b0));
  assert property (cb (yIn[5] && (yIn[4:0] != 5'b00000)) |-> (yOut[5] == 1'b1));
  assert property (cb (yIn == 6'b100000) |-> (yOut == 6'b000000));

  // X/Z propagation sanity: clean out if input is clean
  assert property (cb (!$isunknown(yIn)) |-> (!$isunknown(yOut)));

  // Minimal functional coverage
  cover property (cb !yIn[5] && (yOut == yIn));                          // pass-through path
  cover property (cb yIn[5] && (yIn[4:0] != 5'b0) && (yOut[5] == 1'b1)); // transform path
  cover property (cb yIn == 6'b100000 && yOut == 6'b000000);             // min negative corner
  cover property (cb yIn == 6'b011111 && yOut == 6'b011111);             // max positive
  cover property (cb yIn == 6'b111111 && yOut == ({1'b1, ~5'b11111} + 6'b000001)); // -1 case
endmodule

// Bind to DUT (includes internal net)
bind MyTruthComplement MyTruthComplement_sva i_MyTruthComplement_sva(
  .yIn(yIn),
  .yOut(yOut),
  .inverted_yIn(inverted_yIn)
);