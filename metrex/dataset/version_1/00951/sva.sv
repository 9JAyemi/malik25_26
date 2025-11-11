// SVA for comparator: concise, full functional checking with coverage.
// Bind this file to the DUT.

module comparator_sva (
  input  logic [3:0] A,
  input  logic [3:0] B,
  input  logic       EQ,
  input  logic       GT,
  input  logic       LT
);

  // Guard assertions when inputs are known; sample on input change and evaluate after delta
  // Core functional equivalence: outputs must exactly match the relation of A and B
  assert property (@(A or B) disable iff ($isunknown({A,B}))
                   ##0 ((EQ == (A==B)) && (GT == (A>B)) && (LT == (A<B))))
    else $error("comparator: outputs not matching A vs B relation");

  // Exactly one output must be 1 whenever inputs are known
  assert property (@(A or B or EQ or GT or LT) disable iff ($isunknown({A,B}))
                   ##0 $onehot({EQ,GT,LT}))
    else $error("comparator: outputs not onehot");

  // No X/Z on outputs when inputs are known
  assert property (@(A or B) disable iff ($isunknown({A,B}))
                   ##0 !$isunknown({EQ,GT,LT}))
    else $error("comparator: X/Z detected on outputs with known inputs");

  // Coverage: hit all three relation cases
  cover property (@(A or B) disable iff ($isunknown({A,B})) ##0 (A==B && EQ && !GT && !LT));
  cover property (@(A or B) disable iff ($isunknown({A,B})) ##0 (A>B  && GT && !EQ && !LT));
  cover property (@(A or B) disable iff ($isunknown({A,B})) ##0 (A<B  && LT && !EQ && !GT));

  // Boundary coverage: min/max corners
  cover property (@(A or B) ##0 (A==4'd0  && B==4'd0  && EQ));
  cover property (@(A or B) ##0 (A==4'd15 && B==4'd15 && EQ));
  cover property (@(A or B) ##0 (A==4'd0  && B==4'd15 && LT));
  cover property (@(A or B) ##0 (A==4'd15 && B==4'd0  && GT));

endmodule

bind comparator comparator_sva sva_cmp (.A(A), .B(B), .EQ(EQ), .GT(GT), .LT(LT));