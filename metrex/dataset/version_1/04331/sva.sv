// SVA for and4. Bind this to the DUT.
module and4_sva (
  input logic A, B, C, D, X,
  input logic w1, w2, w3
);
  // Guard for $past/$changed use
  bit past_valid;
  initial past_valid = 0;
  always @(A or B or C or D or X) past_valid = 1;

  // Functional correctness and internal chain equivalence (4-state exact)
  assert property (@(A or B or C or D or w1 or w2 or w3)
                   1 |-> ##0 (w1 === (A & B) && w2 === w1 && w3 === w2 && X === w3));
  // Direct external behavior check
  assert property (@(A or B) 1 |-> ##0 (X === (A & B)));

  // Independence: C/D must not affect X (with A/B held)
  assert property (disable iff (!past_valid)
                   @(posedge C or negedge C or posedge D or negedge D)
                   (A==$past(A) && B==$past(B)) |-> X==$past(X));

  // Any X change must be due to A or B changing (never due to C/D)
  assert property (disable iff (!past_valid)
                   @(posedge X or negedge X)
                   ($changed(A) || $changed(B)));

  // Coverage: all AB minterms with correct X
  cover property (@(A or B) ##0 (A==0 && B==0 && X==0));
  cover property (@(A or B) ##0 (A==0 && B==1 && X==0));
  cover property (@(A or B) ##0 (A==1 && B==0 && X==0));
  cover property (@(A or B) ##0 (A==1 && B==1 && X==1));

  // Coverage: X toggles observed
  cover property (@(posedge X) 1);
  cover property (@(negedge X) 1);

  // Coverage: exercise C/D activity while demonstrating X stability
  cover property (disable iff (!past_valid)
                  @(posedge C or negedge C or posedge D or negedge D)
                  (A==$past(A) && B==$past(B)) ##0 $stable(X));
endmodule

bind and4 and4_sva u_and4_sva (.*);