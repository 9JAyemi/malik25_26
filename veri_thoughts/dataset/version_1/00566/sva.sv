// SVA for OAI21X1: Y = ~((A | B) & C)
module OAI21X1_sva (input logic A, B, C, Y);

  // Functional equivalence (allow a delta for propagation)
  property p_func;
    @(A or B or C or Y) 1 |-> ##0 (Y === ~((A | B) & C));
  endproperty
  assert property (p_func);

  // Y must be known whenever inputs are known
  assert property (@(A or B or C or Y) (!$isunknown({A,B,C})) |-> ##0 (!$isunknown(Y)));

  // Useful simplified checks
  assert property (@(A or B or C or Y) (C == 1'b0) |-> ##0 (Y == 1'b1));
  assert property (@(A or B or C or Y) (C == 1'b1) |-> ##0 (Y === ~(A | B)));

  // Truth-table coverage (all minterms)
  cover property (@(A or B or C) (A==0 && B==0 && C==0 && Y==1));
  cover property (@(A or B or C) (A==0 && B==1 && C==0 && Y==1));
  cover property (@(A or B or C) (A==1 && B==0 && C==0 && Y==1));
  cover property (@(A or B or C) (A==1 && B==1 && C==0 && Y==1));
  cover property (@(A or B or C) (A==0 && B==0 && C==1 && Y==1));
  cover property (@(A or B or C) (A==0 && B==1 && C==1 && Y==0));
  cover property (@(A or B or C) (A==1 && B==0 && C==1 && Y==0));
  cover property (@(A or B or C) (A==1 && B==1 && C==1 && Y==0));

  // Key transition coverage
  cover property (@(A or B or C) $rose(C) && (A||B) ##0 (Y==0));
  cover property (@(A or B or C) $fell(C) ##0 (Y==1));
  cover property (@(A or B or C) $rose(A) && C ##0 (Y==0));
  cover property (@(A or B or C) $rose(B) && C ##0 (Y==0));
  cover property (@(A or B or C) (C && !A && !B) ##0 (Y==1));

endmodule

// Bind into the DUT
bind OAI21X1 OAI21X1_sva oai21x1_sva_i (.*);