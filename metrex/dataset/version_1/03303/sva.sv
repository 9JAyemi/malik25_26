// SVA checker for comparator_3bit
module comparator_3bit_sva (
  input logic [2:0] A,
  input logic [2:0] B,
  input logic       EQ
);

  // Functional equivalence, X-prop, and branch checks
  always_comb begin
    // Exact behavioral match (including X-propagation)
    assert #0 (EQ === ((A == B) ? 1'b1 : 1'b0))
      else $error("EQ mismatch: A=%0d B=%0d EQ=%b", A, B, EQ);

    // Known inputs -> known output
    if (!$isunknown({A,B}))
      assert #0 (!$isunknown(EQ))
        else $error("EQ is X with known inputs: A=%0d B=%0d", A, B);

    // Any unknown on inputs -> EQ must be X (given ?: arms differ)
    if ($isunknown({A,B}))
      assert #0 ($isunknown(EQ))
        else $error("EQ should be X when inputs have X/Z: A=%b B=%b", A, B);

    // Explicit true/false branches for non-X cases
    if (A == B)
      assert #0 (EQ === 1'b1) else $error("EQ!=1 when A==B: A=%0d", A);
    else if (A != B)
      assert #0 (EQ === 1'b0) else $error("EQ!=0 when A!=B: A=%0d B=%0d", A, B);
  end

  // Concise coverage
  always_comb begin
    // Hit both outcomes
    cover (A == B && EQ === 1'b1);
    cover (A != B && EQ === 1'b0);
    // X-propagation seen
    cover ($isunknown({A,B}) && $isunknown(EQ));
    // Hit all 8 equal-value cases
    cover (A === 3'd0 && B === 3'd0 && EQ === 1'b1);
    cover (A === 3'd1 && B === 3'd1 && EQ === 1'b1);
    cover (A === 3'd2 && B === 3'd2 && EQ === 1'b1);
    cover (A === 3'd3 && B === 3'd3 && EQ === 1'b1);
    cover (A === 3'd4 && B === 3'd4 && EQ === 1'b1);
    cover (A === 3'd5 && B === 3'd5 && EQ === 1'b1);
    cover (A === 3'd6 && B === 3'd6 && EQ === 1'b1);
    cover (A === 3'd7 && B === 3'd7 && EQ === 1'b1);
  end

endmodule

bind comparator_3bit comparator_3bit_sva u_comparator_3bit_sva (.A(A), .B(B), .EQ(EQ));