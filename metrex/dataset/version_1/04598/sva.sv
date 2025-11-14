// SVA for module r0
module r0_sva (
  input clk_sys,
  input strob1b,
  input [0:15] w,
  input zs, s_1, s0, carry, vl, vg, exy, exx,
  input ust_z, ust_v, ust_mc, ust_y, ust_x, cleg,
  input w_zmvc, w_legy, lrp,
  input _0_v,
  input zer,
  input [0:15] r0
);

  // recompute strobed controls
  wire c0 = ust_z  & strob1b;
  wire c1 = ust_mc & strob1b;
  wire c2 = ust_v  & strob1b;
  wire c7 = ust_y  & strob1b;
  wire c8 = ust_x  & strob1b;

  default clocking cb @ (posedge clk_sys); endclocking

  // reset behavior
  ap_rst_async: assert property (@(posedge zer) r0 == 16'b0);
  ap_rst_hold:  assert property (zer |-> (r0 == 16'b0));

  // {0,1,3} write via w_zmvc
  ap_013_wzmvc: assert property (disable iff (zer || $past(zer))
                                 $past(w_zmvc) |-> {r0[0:1], r0[3]} == $past({w[0:1], w[3]}));
  // bit 0 via c0 when no w_zmvc
  ap_0_c0:      assert property (disable iff (zer || $past(zer))
                                 $past(!w_zmvc && c0) |-> r0[0] == $past(zs));
  // bits 1,3 via c1 when no w_zmvc
  ap_13_c1:     assert property (disable iff (zer || $past(zer))
                                 $past(!w_zmvc && c1) |-> {r0[1], r0[3]} == $past({s_1, carry}));
  // hold when not written
  ap_0_hold:    assert property (disable iff (zer || $past(zer))
                                 $past(!w_zmvc && !c0) |-> r0[0] == $past(r0[0]));
  ap_1_hold:    assert property (disable iff (zer || $past(zer))
                                 $past(!w_zmvc && !c1) |-> r0[1] == $past(r0[1]));
  ap_3_hold:    assert property (disable iff (zer || $past(zer))
                                 $past(!w_zmvc && !c1) |-> r0[3] == $past(r0[3]));

  // bit 2 priority chain: _0_v > w_zmvc > (c2 & (s0 ^ s_1)) > hold
  ap_2_zero:    assert property (disable iff (zer || $past(zer))
                                 $past(_0_v) |-> r0[2] == 1'b0);
  ap_2_wzmvc:   assert property (disable iff (zer || $past(zer))
                                 $past(! _0_v && w_zmvc) |-> r0[2] == $past(w[2]));
  ap_2_c2:      assert property (disable iff (zer || $past(zer))
                                 $past(! _0_v && !w_zmvc && c2 && (s0 ^ s_1)) |-> r0[2] == 1'b1);
  ap_2_hold:    assert property (disable iff (zer || $past(zer))
                                 $past(! _0_v && !w_zmvc && !(c2 && (s0 ^ s_1)))
                                 |-> r0[2] == $past(r0[2]));

  // [4:7] path: w_legy > independent cleg (4:6) and c7 (7)
  ap_47_w:      assert property (disable iff (zer || $past(zer))
                                 $past(w_legy) |-> r0[4:7] == $past(w[4:7]));
  ap_46_cleg:   assert property (disable iff (zer || $past(zer))
                                 $past(!w_legy && cleg) |-> r0[4:6] == $past({vl, zs, vg}));
  ap_7_c7:      assert property (disable iff (zer || $past(zer))
                                 $past(!w_legy && c7) |-> r0[7] == $past(exy));
  ap_46_hold:   assert property (disable iff (zer || $past(zer))
                                 $past(!w_legy && !cleg) |-> r0[4:6] == $past(r0[4:6]));
  ap_7_hold:    assert property (disable iff (zer || $past(zer))
                                 $past(!w_legy && !c7) |-> r0[7] == $past(r0[7]));

  // [8:15] path: lrp > c8(only bit8)
  ap_815_lrp:   assert property (disable iff (zer || $past(zer))
                                 $past(lrp) |-> r0[8:15] == $past(w[8:15]));
  ap_8_c8:      assert property (disable iff (zer || $past(zer))
                                 $past(!lrp && c8) |-> r0[8] == $past(exx));
  ap_8_hold:    assert property (disable iff (zer || $past(zer))
                                 $past(!lrp && !c8) |-> r0[8] == $past(r0[8]));
  ap_915_hold:  assert property (disable iff (zer || $past(zer))
                                 $past(!lrp) |-> r0[9:15] == $past(r0[9:15]));

  // key scenario covers
  cp_rst:       cover property ($rose(zer));
  cp_013_w:     cover property (w_zmvc);
  cp_0_c0:      cover property (!w_zmvc && c0);
  cp_13_c1:     cover property (!w_zmvc && c1);
  cp_2__0v:     cover property (_0_v);
  cp_2_w:       cover property (! _0_v && w_zmvc);
  cp_2_c2:      cover property (! _0_v && !w_zmvc && c2 && (s0 ^ s_1));
  cp_47_w:      cover property (w_legy);
  cp_46_cleg:   cover property (!w_legy && cleg);
  cp_7_c7:      cover property (!w_legy && c7);
  cp_815_lrp:   cover property (lrp);
  cp_8_c8:      cover property (!lrp && c8);
  cp_both_cleg_c7: cover property (!w_legy && cleg && c7);
  cp_lrp_c8:      cover property (lrp && c8);

endmodule

bind r0 r0_sva r0_sva_i (.*);