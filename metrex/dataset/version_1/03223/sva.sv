// SVA for my_module: concise, high-quality checks and coverage

module my_module_sva;

  // Functional equivalence (4-state). Sample on any relevant change
  a_func:  assert property (@(A1 or A2 or B1 or B2 or Y)
                            Y === ((A1 & A2) | (B1 & B2)));

  // Internal net correctness (structural checks, 4-state)
  a_nand0: assert property (@(A1 or A2 or nand0_out)
                            nand0_out === ~(A1 & A2));
  a_nand1: assert property (@(B1 or B2 or nand1_out)
                            nand1_out === ~(B1 & B2));
  a_and0:  assert property (@(nand0_out or nand1_out or and0_out_Y)
                            and0_out_Y === (nand0_out & nand1_out));
  a_not0:  assert property (@(and0_out_Y or and1_out_Y)
                            and1_out_Y === ~and0_out_Y);
  a_buf0:  assert property (@(and1_out_Y or Y)
                            Y === and1_out_Y);

  // Known-inputs => known and correct output (2-state compare)
  a_known: assert property (@(A1 or A2 or B1 or B2 or Y)
                            !$isunknown({A1,A2,B1,B2}) |-> ##0 (! $isunknown(Y) &&
                            (Y == ((A1 & A2) | (B1 & B2)))));

  // Dominance: either AND term high forces Y=1
  a_dom_a: assert property (@(A1 or A2 or Y) (A1 & A2) |-> ##0 (Y == 1'b1));
  a_dom_b: assert property (@(B1 or B2 or Y) (B1 & B2) |-> ##0 (Y == 1'b1));

  // Functional coverage (all quadrants with known inputs)
  c_y0:     cover property (@(A1 or A2 or B1 or B2 or Y)
                            !$isunknown({A1,A2,B1,B2}) && !(A1 & A2) && !(B1 & B2) && (Y == 1'b0));
  c_y1_a:   cover property (@(A1 or A2 or B1 or B2 or Y)
                            !$isunknown({A1,A2,B1,B2}) &&  (A1 & A2) && !(B1 & B2) && (Y == 1'b1));
  c_y1_b:   cover property (@(A1 or A2 or B1 or B2 or Y)
                            !$isunknown({A1,A2,B1,B2}) && !(A1 & A2) &&  (B1 & B2) && (Y == 1'b1));
  c_y1_ab:  cover property (@(A1 or A2 or B1 or B2 or Y)
                            !$isunknown({A1,A2,B1,B2}) &&  (A1 & A2) &&  (B1 & B2) && (Y == 1'b1));
  // Edge coverage and X-prop observation
  c_rise:   cover property (@(posedge Y) 1);
  c_fall:   cover property (@(negedge Y) 1);
  c_yx:     cover property (@(A1 or A2 or B1 or B2 or Y) $isunknown(Y));

endmodule

bind my_module my_module_sva sva_my_module();