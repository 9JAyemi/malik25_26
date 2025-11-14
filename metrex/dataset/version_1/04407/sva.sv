// SVA checker for adder_subtractor
module adder_subtractor_sva (
  input  logic [3:0] A, B,
  input  logic       C,
  input  logic [3:0] S,
  input  logic       OVF,
  // internal nets (bound by name)
  input  logic [3:0] B_neg,
  input  logic [3:0] C_neg,
  input  logic [3:0] B_neg_plus_1,
  input  logic [3:0] B_minus_C,
  input  logic [3:0] A_plus_B,
  input  logic [3:0] A_minus_B
);

  always_comb begin
    automatic logic [3:0] exp_add = A + B;
    automatic logic [3:0] exp_sub = A + (~B + 4'd1);
    automatic logic       exp_ovf_add = (A[3]==B[3]) && (exp_add[3] != A[3]);
    automatic logic       exp_ovf_sub = (A[3]!=B[3]) && (exp_sub[3] != A[3]);

    // X-prop guard
    if (!$isunknown({A,B,C})) assert #0 (!$isunknown({S,OVF})) else $error("X/Z on outputs with known inputs");

    // Datapath select
    if (C==1'b0) begin
      assert #0 (S == exp_add) else $error("Add result mismatch");
      assert #0 (S == A_plus_B) else $error("S != A_plus_B");
    end else begin
      assert #0 (S == exp_sub) else $error("Sub result mismatch");
      assert #0 (S == A_minus_B) else $error("S != A_minus_B");
    end

    // Overflow correctness (2's complement rule)
    assert #0 (OVF == (C ? exp_ovf_sub : exp_ovf_add))
      else $error("OVF mismatch");

    // No-overflow cases
    if (C==1'b0 && (A[3] != B[3])) assert #0 (!OVF) else $error("Unexpected OVF on add with opposite signs");
    if (C==1'b1 && (A[3] == B[3])) assert #0 (!OVF) else $error("Unexpected OVF on sub with same signs");

    // Internal nets consistency
    assert #0 (B_neg == (~B + 4'd1)) else $error("B_neg mismatch");
    assert #0 (B_neg_plus_1 == (B_neg + 4'd1)) else $error("B_neg_plus_1 mismatch");
    assert #0 (A_plus_B == (A + B)) else $error("A_plus_B mismatch");
    assert #0 (A_minus_B == (A + (~B + 4'd1))) else $error("A_minus_B mismatch");
    // As coded, C_neg equals (C ? 1 : 2) on 4 bits; and B_minus_C uses that
    assert #0 (C_neg == (C ? 4'd1 : 4'd2)) else $error("C_neg mismatch");
    assert #0 (B_minus_C == (B + C_neg)) else $error("B_minus_C mismatch");

    // Simple identities
    if (B==4'd0) assert #0 (S == A) else $error("Add/Sub by 0 failed");
    if (C==1'b1 && A==B) assert #0 (S == 4'd0 && !OVF) else $error("A-B when A==B failed");
    if (C==1'b0 && B==(~A + 4'd1)) assert #0 (S == 4'd0) else $error("A+(-A) != 0");

    // Functional coverage
    cover (C==0);
    cover (C==1);
    cover (S==4'd0);
    cover (S[3]==0);
    cover (S[3]==1);
    cover (C==0 && OVF);
    cover (C==1 && OVF);
    cover (C==0 && A[3]==0 && B[3]==0 && OVF); // pos+pos -> neg
    cover (C==0 && A[3]==1 && B[3]==1 && OVF); // neg+neg -> pos
    cover (C==1 && A[3]==0 && B[3]==1 && OVF); // pos - neg -> neg
    cover (C==1 && A[3]==1 && B[3]==0 && OVF); // neg - pos -> pos
    cover (C==0 && A==4'h7 && B==4'h1 && OVF);
    cover (C==1 && A==4'h8 && B==4'h1 && OVF);
  end

endmodule

// Bind into DUT scope; name-based connection pulls in internals too
bind adder_subtractor adder_subtractor_sva sva_i (.*);