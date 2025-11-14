// SVA checker for five_to_one. Bind this to the DUT instance.
// Focus: functional equivalence, partitioned cases, X-safety, and concise coverage.

module five_to_one_sva (
  input logic A1, A2, A3,
  input logic B1, B2,
  input logic X,
  input logic VPB, VPWR, VGND, VNB
);
  // Combinational clocking event on any input change
  event comb_ev; always @* -> comb_ev;

  // Power-good gating
  wire pwr_good = (VPWR===1'b1) && (VGND===1'b0) && (VPB===1'b1) && (VNB===1'b0);

  // Local recompute of terms
  wire a_high = A1 & A2 & A3;
  wire b_low  = ~B1 & ~B2;
  wire b_high =  B1 &  B2;

  default clocking cb @(comb_ev); endclocking
  default disable iff (!pwr_good);

  // Functional equivalence (golden equation)
  assert property ( X == ((a_high & b_low) | ((~a_high) & b_high)) );

  // Partitioned, readable checks
  assert property ( b_low  |-> (X ==  a_high) );
  assert property ( b_high |-> (X == ~a_high) );
  assert property ( (B1 ^ B2) |-> (X == 1'b0) );

  // X cannot be 1 unless one of the two product terms is active
  assert property ( X |-> ((a_high & b_low) || ((~a_high) & b_high)) );

  // No X/Z on output when inputs are known and power is good
  assert property ( !$isunknown({A1,A2,A3,B1,B2}) |-> !$isunknown(X) );

  // Sanity: product terms are disjoint
  assert property ( !(b_low && b_high) );

  // Minimal, high-value coverage
  cover property ( pwr_good );
  cover property ( a_high && b_low  && X );           // X=1 via A_high & B=00
  cover property ( !a_high && b_high && X );          // X=1 via ~A_high & B=11
  cover property ( (B1 ^ B2) && (X==1'b0) );          // Mixed B gives X=0
endmodule

// Example bind (place in a package or a separate SVA file)
// bind five_to_one five_to_one_sva five_to_one_sva_i (.*);