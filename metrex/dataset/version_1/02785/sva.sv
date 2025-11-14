// SVA for jcarrylookaheadadder
// Concise, high-quality checks and useful coverage for a 4-bit adder

module jcarrylookaheadadder_sva
(
  input  logic [3:0] A, B,
  input  logic       carryin,
  input  logic [3:0] Y,
  input  logic       carryout
);

  // Recompute expected results (golden model)
  logic [4:0] exp_sum;
  logic c0, c1, c2, c3, c4;
  always_comb begin
    exp_sum = {1'b0, A} + {1'b0, B} + carryin;
    c0 = carryin;
    c1 = (A[0] & B[0]) | ((A[0] ^ B[0]) & c0);
    c2 = (A[1] & B[1]) | ((A[1] ^ B[1]) & c1);
    c3 = (A[2] & B[2]) | ((A[2] ^ B[2]) & c2);
    c4 = (A[3] & B[3]) | ((A[3] ^ B[3]) & c3);
  end

  // Basic X/Z sanitation on inputs; outputs must be known for known inputs
  always_comb begin
    assert (!$isunknown({A,B,carryin}))
      else $error("jcla: Inputs contain X/Z: A=%b B=%b Cin=%b", A, B, carryin);

    if (!$isunknown({A,B,carryin})) begin
      // Vector-level correctness: 5-bit sum matches
      assert (#0 {carryout, Y} == exp_sum)
        else $error("jcla: Sum mismatch. A=%h B=%h Cin=%b exp={C=%b,Y=%h} got={C=%b,Y=%h}",
                    A, B, carryin, exp_sum[4], exp_sum[3:0], carryout, Y);

      // Bit-level correctness using carry chain
      assert (#0 (Y[0] == (A[0]^B[0]^c0) &&
                  Y[1] == (A[1]^B[1]^c1) &&
                  Y[2] == (A[2]^B[2]^c2) &&
                  Y[3] == (A[3]^B[3]^c3) &&
                  carryout == c4))
        else $error("jcla: Bit-level mismatch vs carry chain. A=%h B=%h Cin=%b", A, B, carryin);

      // Carryout must equal MSB of golden sum (redundant but sharp)
      assert (#0 carryout == exp_sum[4])
        else $error("jcla: Carryout mismatch. exp=%b got=%b", exp_sum[4], carryout);
    end
  end

  // Functional coverage (exercise key scenarios)
  always_comb begin
    if (!$isunknown({A,B,carryin})) begin
      cover (#0 carryin == 0);
      cover (#0 carryin == 1);
      cover (#0 exp_sum[4]);                // carry generated
      cover (#0 exp_sum == 5'b0_0000);      // 0+0+0
      cover (#0 exp_sum == 5'b1_1111);      // 15+15+1
      cover (#0 ((A^B)==4'hF) && ((A&B)==4'h0) && carryin==1); // full propagate chain
      cover (#0 (c1 && c2 && c3 && c4));    // ripple through all stages
    end
  end

endmodule

// Bind into DUT
bind jcarrylookaheadadder jcarrylookaheadadder_sva sva_inst(
  .A(A), .B(B), .carryin(carryin), .Y(Y), .carryout(carryout)
);