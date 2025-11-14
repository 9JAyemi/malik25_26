// SVA for o311ai: bindable, concise, full functional and structural checks + coverage

module o311ai_sva;

  // Functional equivalence (spec)
  a_func: assert property (@(A1 or A2 or A3 or B1 or C1 or Y)
    Y == ((A2 | (A1 & B1)) & ~A3 & C1));

  // Structural gate checks
  a_n1: assert property (@(A1 or B1 or n1) n1 == (A1 & B1));
  a_n2: assert property (@(A2 or n1 or n2) n2 == (A2 | n1));
  a_n3: assert property (@(A3 or n3) n3 == ~A3);
  a_Yg: assert property (@(n2 or n3 or C1 or Y) Y == (n2 & n3 & C1));

  // Known-value checks
  a_inputs_known:   assert property (@(A1 or A2 or A3 or B1 or C1) !$isunknown({A1,A2,A3,B1,C1}));
  a_internals_known:assert property (@(n1 or n2 or n3)              !$isunknown({n1,n2,n3}));
  a_output_known:   assert property (@(Y)                           !$isunknown(Y));

  // Key implications
  a_block_C1: assert property (@(C1 or Y) !C1 |-> !Y);
  a_block_A3: assert property (@(A3 or Y)  A3 |-> !Y);
  a_path_A2:  assert property (@(A2 or A3 or C1 or Y) (C1 & !A3 & A2) |-> Y);
  a_path_AB:  assert property (@(A1 or B1 or A2 or A3 or C1 or Y) (C1 & !A3 & !A2 & A1 & B1) |-> Y);

  // Coverage: hit both ways to 1, and principal 0-causes, plus Y toggles
  c_y1_via_A2: cover property (@(A1 or A2 or A3 or B1 or C1 or Y) C1 & !A3 & A2 & Y);
  c_y1_via_AB: cover property (@(A1 or A2 or A3 or B1 or C1 or Y) C1 & !A3 & !A2 & A1 & B1 & Y);
  c_y0_via_A3: cover property (@(A3 or Y)  A3 & !Y);
  c_y0_via_C1: cover property (@(C1 or Y) !C1 & !Y);
  c_y0_via_inputs: cover property (@(A1 or A2 or A3 or B1 or C1 or Y)
                                   C1 & !A3 & !A2 & !(A1 & B1) & !Y);
  c_y_rise: cover property (@(Y) $rose(Y));
  c_y_fall: cover property (@(Y) $fell(Y));

endmodule

bind o311ai o311ai_sva o311ai_sva_i();