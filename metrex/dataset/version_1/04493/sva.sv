// SVA for Mux12: concise, high-quality checks and coverage
module Mux12_sva(
  input logic [11:0] A, B, C, D,
  input logic        S0, S1,
  input logic [11:0] O,
  input logic [11:0] AB, CD,
  input logic        sel
);
  default clocking cb @(*); endclocking

  // Local correctness of each internal computation (gate on only relevant known inputs)
  a_sel: assert property ( !$isunknown({S0,S1}) |-> sel == (S1 ? S0 : ~S0) );
  a_ab:  assert property ( !$isunknown({S0,A,B}) |-> AB  == (S0 ? A  : B ) );
  a_cd:  assert property ( !$isunknown({S0,C,D}) |-> CD  == (S0 ? C  : D ) );
  a_o:   assert property ( !$isunknown({sel,AB,CD}) |-> O == (sel ? AB : CD) );

  // Functional path coverage for each select combination
  c_00_B: cover property ( !$isunknown({B,S0,S1}) && (S1==0) && (S0==0) && (O==B) );
  c_01_C: cover property ( !$isunknown({C,S0,S1}) && (S1==0) && (S0==1) && (O==C) );
  c_10_D: cover property ( !$isunknown({D,S0,S1}) && (S1==1) && (S0==0) && (O==D) );
  c_11_A: cover property ( !$isunknown({A,S0,S1}) && (S1==1) && (S0==1) && (O==A) );
endmodule

bind Mux12 Mux12_sva u_sva(
  .A(A), .B(B), .C(C), .D(D),
  .S0(S0), .S1(S1),
  .O(O), .AB(AB), .CD(CD), .sel(sel)
);