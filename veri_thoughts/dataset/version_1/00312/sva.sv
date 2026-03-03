// SVA bind file for top_module and submodules
// Concise, functionally complete checks with key coverage

// -------------------- top_module SVA --------------------
module top_module_sva(
  input  logic [3:0] A, B,
  input  logic       CIN,
  input  logic [3:0] SUM,
  input  logic       COUT,
  input  logic       LT,
  // internal wires
  input  logic [3:0] adder_sum,
  input  logic       adder_cout,
  input  logic       lt_int
);
  // Wiring equivalence (sample after delta to avoid preponed race)
  assert property (@(A or B or CIN or adder_sum or adder_cout or lt_int)
                   1 |-> ##0 (SUM  == adder_sum));
  assert property (@(A or B or CIN or adder_sum or adder_cout or lt_int)
                   1 |-> ##0 (COUT == adder_cout));
  assert property (@(A or B or CIN or adder_sum or adder_cout or lt_int)
                   1 |-> ##0 (LT   == lt_int));

  // End-to-end golden model checks
  assert property (@(A or B or CIN) 1 |-> ##0 ({COUT,SUM} == A + B + CIN));
  assert property (@(A or B)        1 |-> ##0 (LT == (A < B)));

  // X-propagation guard
  assert property (@(A or B or CIN)
                   !$isunknown({A,B,CIN}) |-> ##0 !$isunknown({SUM,COUT,LT}));

  // Minimal, meaningful functional coverage
  cover property (@(A or B or CIN) 1 |-> ##0 (COUT == 1));            // overflow seen
  cover property (@(A or B)        1 |-> ##0 (LT == 1));              // A < B seen
  cover property (@(A or B)        1 |-> ##0 ((A==B) && (LT == 0)));  // A == B seen
  cover property (@(A or B)        1 |-> ##0 ((A>B) && (LT == 0)));   // A > B seen
  // Long propagate chain (all bits propagate and CIN=1 -> carry ripples through)
  cover property (@(A or B or CIN) ((&(A^B)) && CIN) |-> ##0 (COUT == 1));
endmodule
bind top_module top_module_sva u_top_module_sva(
  .A(A), .B(B), .CIN(CIN), .SUM(SUM), .COUT(COUT), .LT(LT),
  .adder_sum(adder_sum), .adder_cout(adder_cout), .lt_int(lt)
);


// -------------------- ripple_carry_adder SVA --------------------
module ripple_carry_adder_sva(
  input  logic [3:0] A, B,
  input  logic       CIN,
  input  logic [3:0] SUM,
  input  logic       COUT,
  // internal wires
  input  logic [3:0] fa1_sum, fa2_sum, fa3_sum, fa4_sum,
  input  logic       fa1_cout, fa2_cout, fa3_cout
);
  // Bit 0
  assert property (@(A or B or CIN)
                   1 |-> ##0 (fa1_sum[0] == (A[0]^B[0]^CIN)));
  assert property (@(A or B or CIN)
                   1 |-> ##0 (fa1_cout   == ((A[0]&B[0])|(A[0]&CIN)|(B[0]&CIN))));

  // Bit 1
  assert property (@(A or B or CIN or fa1_cout)
                   1 |-> ##0 (fa2_sum[1] == (A[1]^B[1]^fa1_cout)));
  assert property (@(A or B or CIN or fa1_cout)
                   1 |-> ##0 (fa2_cout   == ((A[1]&B[1])|(A[1]&fa1_cout)|(B[1]&fa1_cout))));

  // Bit 2
  assert property (@(A or B or CIN or fa2_cout)
                   1 |-> ##0 (fa3_sum[2] == (A[2]^B[2]^fa2_cout)));
  assert property (@(A or B or CIN or fa2_cout)
                   1 |-> ##0 (fa3_cout   == ((A[2]&B[2])|(A[2]&fa2_cout)|(B[2]&fa2_cout))));

  // Bit 3 and final carry
  assert property (@(A or B or CIN or fa3_cout)
                   1 |-> ##0 (fa4_sum[3] == (A[3]^B[3]^fa3_cout)));
  assert property (@(A or B or CIN or fa3_cout)
                   1 |-> ##0 (COUT       == ((A[3]&B[3])|(A[3]&fa3_cout)|(B[3]&fa3_cout))));

  // Sum packing
  assert property (@(A or B or CIN or fa1_sum or fa2_sum or fa3_sum or fa4_sum)
                   1 |-> ##0 (SUM == {fa4_sum[3], fa3_sum[2], fa2_sum[1], fa1_sum[0]}));

  // End-to-end equivalence
  assert property (@(A or B or CIN) 1 |-> ##0 ({COUT,SUM} == A + B + CIN));

  // X-propagation guard
  assert property (@(A or B or CIN)
                   !$isunknown({A,B,CIN}) |-> ##0 !$isunknown({SUM,COUT}));
endmodule
bind ripple_carry_adder ripple_carry_adder_sva u_rca_sva(
  .A(A), .B(B), .CIN(CIN), .SUM(SUM), .COUT(COUT),
  .fa1_sum(fa1_sum), .fa2_sum(fa2_sum), .fa3_sum(fa3_sum), .fa4_sum(fa4_sum),
  .fa1_cout(fa1_cout), .fa2_cout(fa2_cout), .fa3_cout(fa3_cout)
);


// -------------------- full_adder SVA --------------------
module full_adder_sva(
  input logic A, B, CIN,
  input logic SUM, COUT
);
  assert property (@(A or B or CIN) 1 |-> ##0 (SUM  == (A^B^CIN)));
  assert property (@(A or B or CIN) 1 |-> ##0 (COUT == ((A&B)|(A&CIN)|(B&CIN))));
  assert property (@(A or B or CIN) !$isunknown({A,B,CIN}) |-> ##0 !$isunknown({SUM,COUT}));
  // Simple toggle coverage
  cover property (@(A or B or CIN) 1 |-> ##0 (SUM==0));
  cover property (@(A or B or CIN) 1 |-> ##0 (SUM==1));
endmodule
bind full_adder full_adder_sva u_fa_sva(.A(A), .B(B), .CIN(CIN), .SUM(SUM), .COUT(COUT));


// -------------------- magnitude_comparator SVA --------------------
module magnitude_comparator_sva(
  input logic [3:0] A, B,
  input logic       LT
);
  assert property (@(A or B) 1 |-> ##0 (LT == (A < B)));
  assert property (@(A or B) !$isunknown({A,B}) |-> ##0 !$isunknown(LT));

  // Category coverage
  cover property (@(A or B) 1 |-> ##0 (LT==1));
  cover property (@(A or B) 1 |-> ##0 ((A==B) && (LT==0)));
  cover property (@(A or B) 1 |-> ##0 ((A>B) && (LT==0)));
endmodule
bind magnitude_comparator magnitude_comparator_sva u_cmp_sva(.A(A), .B(B), .LT(LT));