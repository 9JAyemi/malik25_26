// SVA for comparator — event-based (no clock), concise and comprehensive
// Bind this checker to the DUT

module comparator_sva #(parameter WIDTH=4)
(
  input  logic [WIDTH-1:0] A,
  input  logic [WIDTH-1:0] B,
  input  logic             EQ,
  input  logic             GT,
  input  logic             LT,
  input  logic             NE
);

  // Sample on any input change
  localparam string ID = "comparator";
  let valid_in = !$isunknown({A,B});
  let outs     = {EQ,GT,LT,NE};

  // Outputs never X/Z when inputs are known
  assert property (@(A or B) valid_in |=> !$isunknown(outs))
    else $error("%s: outputs X/Z with known inputs", ID);

  // Functional correctness (same-sample)
  assert property (@(A or B)
                   valid_in |=> (EQ == (A==B)) &&
                                (GT == (A>B))  &&
                                (LT == (A<B))  &&
                                (NE == (A!=B)))
    else $error("%s: functional mismatch", ID);

  // Encoded consistency: exactly one of EQ/GT/LT is 1
  assert property (@(A or B) valid_in |=> $onehot({EQ,GT,LT}))
    else $error("%s: EQ/GT/LT not one-hot", ID);

  // NE consistent with others
  assert property (@(A or B) valid_in |=> (NE == ~EQ) && (NE == (GT || LT)))
    else $error("%s: NE inconsistent", ID);

  // Functional coverage of all comparator outcomes
  cover property (@(A or B) valid_in && (A==B) &&  EQ && !GT && !LT && !NE);
  cover property (@(A or B) valid_in && (A>B)  && !EQ &&  GT && !LT &&  NE);
  cover property (@(A or B) valid_in && (A<B)  && !EQ && !GT &&  LT &&  NE);
  // Also cover NE deasserted case explicitly
  cover property (@(A or B) valid_in && !NE);

endmodule

// Bind to the DUT
bind comparator comparator_sva #(.WIDTH(4)) u_comparator_sva (
  .A(A), .B(B), .EQ(EQ), .GT(GT), .LT(LT), .NE(NE)
);