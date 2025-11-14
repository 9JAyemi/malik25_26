// SVA for signed_mag_comp
// Bind these assertions to the DUT; clockless properties fit combinational logic.

module signed_mag_comp_sva (
  input signed [3:0] A,
  input signed [3:0] B,
  input        logic C
);

  // Local spec of DUT behavior (matches RTL intent)
  let signA  = A[3];
  let signB  = B[3];
  let spec_c = (signA==0 && signB==1) ? 1'b1 :
               (signA==1 && signB==0) ? 1'b0 :
               (signA==0 && signB==0) ? (A >= B) :
                                         (A <= B);

  // Functional equivalence (when inputs are known)
  assert property ( !$isunknown({A,B}) |-> (C == spec_c) )
    else $error("signed_mag_comp: C mismatches spec");

  // Output is known when inputs are known
  assert property ( !$isunknown({A,B}) |-> !$isunknown(C) )
    else $error("signed_mag_comp: C is X/Z with known inputs");

  // Optional: explicit sign-different check
  assert property ( (signA ^ signB) |-> (C == ~signA) )
    else $error("signed_mag_comp: sign-different rule violated");

  // Minimal functional coverage (each decision path and both outcomes where applicable)
  cover property ( signA==0 && signB==1 &&  C );          // pos vs neg
  cover property ( signA==1 && signB==0 && !C );          // neg vs pos

  cover property ( signA==0 && signB==0 && (A >  B) &&  C ); // both pos, gt
  cover property ( signA==0 && signB==0 && (A <  B) && !C ); // both pos, lt
  cover property ( signA==0 && signB==0 && (A == B) &&  C ); // both pos, eq

  cover property ( signA==1 && signB==1 && (A <  B) &&  C ); // both neg, lt -> C=1
  cover property ( signA==1 && signB==1 && (A >  B) && !C ); // both neg, gt -> C=0
  cover property ( signA==1 && signB==1 && (A == B) &&  C ); // both neg, eq -> C=1

endmodule

bind signed_mag_comp signed_mag_comp_sva sva_i (.*);