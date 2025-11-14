// SVA for my_4input_nand
module sva_my_4input_nand;

  // Functional spec: Y == ~(A & B & C & D)
  assert property (@(A or B or C or D or Y))
    Y === ~(A & B & C & D);

  // Structural checks for internal netlist
  assert property (@(A or B or C or D or nand1_out))
    nand1_out === ~(A & B & C & D);
  assert property (@(nand1_out or nand2_out))
    nand2_out === ~nand1_out;
  assert property (@(nand2_out or nand3_out))
    nand3_out === ~nand2_out;
  assert property (@(nand1_out or nand3_out or Y))
    (Y === nand3_out) && (Y === nand1_out);

  // No X/Z on Y when inputs are known
  assert property (@(A or B or C or D))
    !$isunknown({A,B,C,D}) |-> !$isunknown(Y);

  // Coverage: both output states reachable
  cover property (@(A or B or C or D))  (A & B & C & D) && (Y == 0);
  cover property (@(A or B or C or D)) !(A & B & C & D) && (Y == 1);

  // Coverage: last-input edge causes Y transition (concise across all inputs)
  cover property (@(A or B or C or D))
    ( (B && C && D && $rose(A)) ||
      (A && C && D && $rose(B)) ||
      (A && B && D && $rose(C)) ||
      (A && B && C && $rose(D)) ) && $past(Y)==1 && Y==0;

  cover property (@(A or B or C or D))
    ( (B && C && D && $fell(A)) ||
      (A && C && D && $fell(B)) ||
      (A && B && D && $fell(C)) ||
      (A && B && C && $fell(D)) ) && $past(Y)==0 && Y==1;

endmodule

bind my_4input_nand sva_my_4input_nand();