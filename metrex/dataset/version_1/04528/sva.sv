// SVA for sky130_fd_sc_lp__or3
// Bind this checker into the DUT
module sky130_fd_sc_lp__or3_sva;
  // sample on any input/output edge; use ##0 to avoid preponed-race
  default clocking cb @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge X or negedge X); endclocking

  // Power rails must be correct
  a_vpwr: assert property (VPWR === 1'b1);
  a_vgnd: assert property (VGND === 1'b0);
  a_vpb:  assert property (VPB  === 1'b1);
  a_vnb:  assert property (VNB  === 1'b0);

  // Functional equivalence (handles X/Z correctly with 4-state equality)
  a_equiv_always: assert property (1'b1 |-> ##0 (X === (A | B | C)));

  // Strong deterministic cases
  a_any1_out1:   assert property ( (A===1 || B===1 || C===1) |-> ##0 (X===1) );
  a_all0_out0:   assert property ( (A===0 && B===0 && C===0) |-> ##0 (X===0) );

  // No spurious outputs
  a_out1_implies_any1: assert property ( X===1 |-> ##0 (A===1 || B===1 || C===1) );
  a_out0_implies_all0: assert property ( X===0 |-> ##0 (A===0 && B===0 && C===0) );

  // Buffer integrity to internal node
  a_buf_matches_internal: assert property (1'b1 |-> ##0 (X === or0_out_X));

  // Input combination coverage (all 8 combos)
  c_000: cover property (1'b1 |-> ##0 ({A,B,C} == 3'b000));
  c_001: cover property (1'b1 |-> ##0 ({A,B,C} == 3'b001));
  c_010: cover property (1'b1 |-> ##0 ({A,B,C} == 3'b010));
  c_011: cover property (1'b1 |-> ##0 ({A,B,C} == 3'b011));
  c_100: cover property (1'b1 |-> ##0 ({A,B,C} == 3'b100));
  c_101: cover property (1'b1 |-> ##0 ({A,B,C} == 3'b101));
  c_110: cover property (1'b1 |-> ##0 ({A,B,C} == 3'b110));
  c_111: cover property (1'b1 |-> ##0 ({A,B,C} == 3'b111));

  // Toggle coverage
  c_a_rise: cover property (A==0 ##1 A==1);
  c_a_fall: cover property (A==1 ##1 A==0);
  c_b_rise: cover property (B==0 ##1 B==1);
  c_b_fall: cover property (B==1 ##1 B==0);
  c_c_rise: cover property (C==0 ##1 C==1);
  c_c_fall: cover property (C==1 ##1 C==0);
  c_x_rise: cover property (X==0 ##1 X==1);
  c_x_fall: cover property (X==1 ##1 X==0);
endmodule

bind sky130_fd_sc_lp__or3 sky130_fd_sc_lp__or3_sva sva_i();