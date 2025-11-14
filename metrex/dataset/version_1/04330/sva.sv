// SVA for section2_schematic
module section2_schematic_sva (
  input logic n63, Z_B, n62,
  input logic Len_int, Ren_int,
  input logic N_1, N_3, Ldir_int, Rdir_int, N_8, N_4
);

  // Structural equivalence of internal nets
  assert property (@(*) Ldir_int == ~n63);
  assert property (@(*) Rdir_int == ~n62);
  assert property (@(*) N_8     == ~Z_B);
  assert property (@(*) N_1     == (n63 & Z_B));
  assert property (@(*) N_3     == (Z_B & n62));
  assert property (@(*) N_4     == (Ldir_int & N_8 & Rdir_int));

  // OR-combine to outputs
  assert property (@(*) Len_int == (N_1 | N_4));
  assert property (@(*) Ren_int == (N_4 | N_3));

  // Functional correctness by mode of Z_B
  assert property (@(*) Z_B  |-> (Len_int == n63            && Ren_int == n62));
  assert property (@(*) !Z_B |-> (Len_int == (~n63 & ~n62)  && Ren_int == (~n63 & ~n62)));

  // No X/Z on derived signals when inputs are known
  assert property (@(*) (!$isunknown({n63,Z_B,n62})) |-> !$isunknown({Len_int,Ren_int,N_1,N_3,N_4,Ldir_int,Rdir_int,N_8}));

  // Input/output truth-table coverage (all 8 combinations)
  cover property (@(*) (!n63 && !Z_B && !n62 &&  Len_int &&  Ren_int));
  cover property (@(*) (!n63 && !Z_B &&  n62 && !Len_int && !Ren_int));
  cover property (@(*) (!n63 &&  Z_B && !n62 && !Len_int && !Ren_int));
  cover property (@(*) (!n63 &&  Z_B &&  n62 && !Len_int &&  Ren_int));
  cover property (@(*) ( n63 && !Z_B && !n62 && !Len_int && !Ren_int));
  cover property (@(*) ( n63 && !Z_B &&  n62 && !Len_int && !Ren_int));
  cover property (@(*) ( n63 &&  Z_B && !n62 &&  Len_int && !Ren_int));
  cover property (@(*) ( n63 &&  Z_B &&  n62 &&  Len_int &&  Ren_int));

  // Toggle coverage on key internal nets and outputs
  cover property (@(*) $rose(N_1));  cover property (@(*) $fell(N_1));
  cover property (@(*) $rose(N_3));  cover property (@(*) $fell(N_3));
  cover property (@(*) $rose(N_4));  cover property (@(*) $fell(N_4));
  cover property (@(*) $rose(Len_int)); cover property (@(*) $fell(Len_int));
  cover property (@(*) $rose(Ren_int)); cover property (@(*) $fell(Ren_int));

endmodule

// Bind into DUT (allows access to internal nets)
bind section2_schematic section2_schematic_sva sva_i (
  .n63(n63), .Z_B(Z_B), .n62(n62),
  .Len_int(Len_int), .Ren_int(Ren_int),
  .N_1(N_1), .N_3(N_3), .Ldir_int(Ldir_int), .Rdir_int(Rdir_int), .N_8(N_8), .N_4(N_4)
);