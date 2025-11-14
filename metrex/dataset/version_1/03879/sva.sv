// SVA checker for comparator_2bit
module comparator_2bit_sva (
  input  logic [1:0] A,
  input  logic [1:0] B,
  input  logic [1:0] EQ,
  input  logic [1:0] GT
);

  // Known-when-known
  assert property (@(A or B)
    !$isunknown({A,B}) |-> !$isunknown({EQ,GT}))
    else $error("Outputs contain X/Z when inputs are known");

  // Bitwise EQ should be XNOR of inputs
  assert property (@(A or B)
    !$isunknown({A,B}) |-> (EQ == ~(A ^ B)))
    else $error("EQ mismatch: expected ~(A^B)");

  // Bitwise GT should reflect per-bit greater-than
  assert property (@(A or B)
    !$isunknown({A,B}) |-> (GT == {A[1]>B[1], A[0]>B[0]}))
    else $error("GT mismatch: expected {A[1]>B[1],A[0]>B[0]}");

  // Per-bit consistency and mutual exclusion
  genvar i;
  generate
    for (i=0; i<2; i++) begin : g_bit
      // Never assert EQ and GT together on the same bit
      assert property (@(A or B) !(EQ[i] && GT[i]))
        else $error("EQ and GT both 1 on bit %0d", i);

      // Relations
      assert property (@(A or B)
        !$isunknown({A[i],B[i]}) && (A[i]==B[i]) |-> (EQ[i] && !GT[i]))
        else $error("Bit %0d equal: EQ should be 1, GT 0", i);

      assert property (@(A or B)
        !$isunknown({A[i],B[i]}) && (A[i]>B[i])  |-> ( GT[i] && !EQ[i]))
        else $error("Bit %0d A>B: GT should be 1, EQ 0", i);

      assert property (@(A or B)
        !$isunknown({A[i],B[i]}) && (A[i]<B[i])  |-> (!GT[i] && !EQ[i]))
        else $error("Bit %0d A<B: GT,EQ should be 0", i);

      // Coverage: exercise all three relations per bit
      cover property (@(A or B) (A[i]==B[i]));
      cover property (@(A or B) (A[i]>B[i]));
      cover property (@(A or B) (A[i]<B[i]));
    end
  endgenerate

  // Cross-bit scenarios worth hitting
  cover property (@(A or B) (A==B));                            // both bits equal
  cover property (@(A or B) ({A[1]>B[1],A[0]>B[0]}==2'b11));    // both bits GT
  cover property (@(A or B) ({A[1]<B[1],A[0]<B[0]}==2'b11));    // both bits LT

  // Optional: cover all 16 input combinations concisely
  generate
    genvar a, b;
    for (a=0; a<4; a++) begin : g_cov_a
      for (b=0; b<4; b++) begin : g_cov_b
        cover property (@(A or B) (A==a[1:0] && B==b[1:0]));
      end
    end
  endgenerate

endmodule

// Bind into the DUT
bind comparator_2bit comparator_2bit_sva u_comparator_2bit_sva (.A(A), .B(B), .EQ(EQ), .GT(GT));