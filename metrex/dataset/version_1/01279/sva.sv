// SVA checker for sky130_fd_sc_hs__a222o
// Function: X = (A1&A2) | (B1&B2) | (~C1 & ~C2)

module sky130_fd_sc_hs__a222o_sva (
  input logic X,
  input logic A1, A2,
  input logic B1, B2,
  input logic C1, C2
);

  // Trigger assertions/covers whenever any input changes
  default clocking cb @(A1 or A2 or B1 or B2 or C1 or C2); endclocking

  // Helper terms
  logic a_and, b_and, c_both0, expr;
  assign a_and   = A1 & A2;
  assign b_and   = B1 & B2;
  assign c_both0 = ~C1 & ~C2;
  assign expr    = a_and | b_and | c_both0;

  // Functional equivalence (4-state consistent). Use ##0 to evaluate after combinational settle.
  assert property (1'b1 |-> ##0 (X === expr))
    else $error("a222o: X mismatches (A1&A2)|(B1&B2)|(~C1&~C2)");

  // No X/Z on output when all inputs are known
  assert property (!$isunknown({A1,A2,B1,B2,C1,C2}) |-> ##0 (!$isunknown(X) && (X == expr)))
    else $error("a222o: X unknown/wrong while inputs are known");

  // Coverage: 8 functional classes (none/each-single/doubles/triple)
  cover property (a_and && !b_and && !c_both0 |-> ##0 X==1);
  cover property (!a_and && b_and && !c_both0 |-> ##0 X==1);
  cover property (!a_and && !b_and && c_both0 |-> ##0 X==1);
  cover property (!a_and && !b_and && !c_both0 |-> ##0 X==0);

  cover property (a_and && b_and && !c_both0 |-> ##0 X==1);
  cover property (a_and && !b_and && c_both0 |-> ##0 X==1);
  cover property (!a_and && b_and && c_both0 |-> ##0 X==1);
  cover property (a_and && b_and && c_both0 |-> ##0 X==1);

  // Output edge coverage
  cover property (1'b1 |-> ##0 $rose(X));
  cover property (1'b1 |-> ##0 $fell(X));

endmodule

bind sky130_fd_sc_hs__a222o sky130_fd_sc_hs__a222o_sva
  (.X(X), .A1(A1), .A2(A2), .B1(B1), .B2(B2), .C1(C1), .C2(C2));