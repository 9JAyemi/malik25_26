// SVA checker for full_adder
module full_adder_sva (
  input logic A, B, Ci,
  input logic S, Co,
  input logic n1, n2, n3
);

  // Functional spec: 2-bit addition
  ap_full_add: assert property (@(A or B or Ci)
    (!$isunknown({A,B,Ci})) |-> ##0 ({Co,S} == A + B + Ci));

  // Gate-level decomposition checks
  ap_n1: assert property (@(A or B or Ci)
    (!$isunknown({A,B,Ci})) |-> ##0 (n1 == (A ^ B)));

  ap_n2: assert property (@(A or B or Ci)
    (!$isunknown({A,B,Ci})) |-> ##0 (n2 == (A & B)));

  ap_n3: assert property (@(A or B or Ci)
    (!$isunknown({A,B,Ci})) |-> ##0 (n3 == (n1 & Ci)));

  ap_s_from_n1: assert property (@(A or B or Ci)
    (!$isunknown({A,B,Ci})) |-> ##0 (S == (n1 ^ Ci)));

  ap_co_from_n2n3: assert property (@(A or B or Ci)
    (!$isunknown({A,B,Ci})) |-> ##0 (Co == (n2 | n3)));

  // Equivalent carry SOP form (factorization cross-check)
  ap_carry_sop: assert property (@(A or B or Ci)
    (!$isunknown({A,B,Ci})) |-> ##0 (Co == ((A & B) | (B & Ci) | (Ci & A))));

  // Functional coverage: exercise all input combinations
  cp_000: cover property (@(A or B or Ci) ##0 {A,B,Ci} == 3'b000);
  cp_001: cover property (@(A or B or Ci) ##0 {A,B,Ci} == 3'b001);
  cp_010: cover property (@(A or B or Ci) ##0 {A,B,Ci} == 3'b010);
  cp_011: cover property (@(A or B or Ci) ##0 {A,B,Ci} == 3'b011);
  cp_100: cover property (@(A or B or Ci) ##0 {A,B,Ci} == 3'b100);
  cp_101: cover property (@(A or B or Ci) ##0 {A,B,Ci} == 3'b101);
  cp_110: cover property (@(A or B or Ci) ##0 {A,B,Ci} == 3'b110);
  cp_111: cover property (@(A or B or Ci) ##0 {A,B,Ci} == 3'b111);

endmodule

// Bind into the DUT (captures internal nets n1,n2,n3)
bind full_adder full_adder_sva sva_full_adder (
  .A(A), .B(B), .Ci(Ci),
  .S(S), .Co(Co),
  .n1(n1), .n2(n2), .n3(n3)
);