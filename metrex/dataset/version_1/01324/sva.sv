// SVA for full_adder: concise, functionally complete
module full_adder_sva (
  input logic A,
  input logic B,
  input logic CI,
  input logic SUM,
  input logic COUT_N
);

  // Useful combinational expressions
  let majority = (A & B) | (A & CI) | (B & CI);

  // Functional correctness when inputs are known (no X/Z)
  assert property (@(A or B or CI or SUM or COUT_N)
                   disable iff ($isunknown({A,B,CI}))
                   (SUM == (A ^ B ^ CI)) && (COUT_N == ~majority));

  // Outputs must not be X/Z when inputs are 0/1
  assert property (@(A or B or CI or SUM or COUT_N)
                   (!$isunknown({A,B,CI})) |-> (!$isunknown({SUM,COUT_N})));

  // Truth-table coverage (inputs observed with expected outputs)
  cover property (@(A or B or CI) (!A && !B && !CI && SUM==0 && COUT_N==1));
  cover property (@(A or B or CI) (!A && !B &&  CI && SUM==1 && COUT_N==1));
  cover property (@(A or B or CI) (!A &&  B && !CI && SUM==1 && COUT_N==1));
  cover property (@(A or B or CI) (!A &&  B &&  CI && SUM==0 && COUT_N==0));
  cover property (@(A or B or CI) ( A && !B && !CI && SUM==1 && COUT_N==1));
  cover property (@(A or B or CI) ( A && !B &&  CI && SUM==0 && COUT_N==0));
  cover property (@(A or B or CI) ( A &&  B && !CI && SUM==0 && COUT_N==0));
  cover property (@(A or B or CI) ( A &&  B &&  CI && SUM==1 && COUT_N==0));

endmodule

// Bind into all instances of full_adder
bind full_adder full_adder_sva u_full_adder_sva (.*);