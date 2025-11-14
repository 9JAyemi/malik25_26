// SVA for mul_bodec_multiplier and mul_bodec_16bit (concise, combinational event-based)

module mul_bodec_multiplier_sva;
  // structural/concat mapping and truncation
  ap_p_partition: assert property (@(p or p_high or p_low) {p_high, p_low} == p);
  ap_p_low_map:   assert property (@(b0 or b1 or b2 or b3 or p_low) p_low  == {b0[1:0], b1, b2, b3, 5'b0});
  ap_p_high_map:  assert property (@(b4 or b5 or b6 or b7 or p_high) p_high == {4'b0,   b4,  b5,  b6,  b7});

  // zeroing and functional mapping vs inputs
  ap_zero_when_x0: assert property (@(a_reg or b_reg) !a_reg[0] |-> (p_high==16'h0 && p_low==16'h0));
  ap_map_when_x1:  assert property (@(a_reg or b_reg)  a_reg[0] |-> (p_low  == {b_reg[1:0], b_reg[5:3], b_reg[8:6], b_reg[11:9], 5'b0}
                                                                   && p_high == {4'b0,      b_reg[14:12], 2'b00,    b_reg[15],    6'b0}));

  // independence from upper bits of a_reg
  ap_ignore_a_hi:  assert property (@(a_reg or b_reg)
                                    ($changed(a_reg[15:1]) && $stable(a_reg[0]) && $stable(b_reg)) |-> $stable({p_high,p_low}));

  // no X on outputs when inputs known
  ap_no_x:         assert property (@(a_reg or b_reg) (!$isunknown({a_reg[0], b_reg})) |-> !$isunknown({p_high, p_low}));

  // simple coverage
  cp_x0:           cover  property (@(a_reg) !a_reg[0]);
  cp_x1:           cover  property (@(a_reg)  a_reg[0]);
  cp_b5_one:       cover  property (@(a_reg or b_reg) a_reg[0] && b_reg[15] && (p_high[6] == 1'b1)); // b5[0] maps to p_high[6]
  cp_nonzero_low:  cover  property (@(a_reg or b_reg) a_reg[0] && (|b_reg[11:0]));
endmodule

bind mul_bodec_multiplier mul_bodec_multiplier_sva mul_bodec_multiplier_sva_i();

module mul_bodec_16bit_sva;
  // gating and grouping
  ap_gate0:        assert property (@(x or b) !x |-> (b0==3'b000 && b1==3'b000 && b2==3'b000 && b3==3'b000 &&
                                                      b4==3'b000 && b5==3'b000 && b6==3'b000 && b7==3'b000));
  ap_gate1:        assert property (@(x or b)  x |-> (b0==b[ 2: 0] && b1==b[ 5: 3] && b2==b[ 8: 6] && b3==b[11: 9] &&
                                                      b4==b[14:12] && b5=={2'b00,b[15]} && b6==3'b000 && b7==3'b000));
  ap_b5_msb0:      assert property (@(x or b) b5[2:1]==2'b00);
  ap_b6_b7_zero:   assert property (@(b6 or b7) b6==3'b000 && b7==3'b000);

  // no X on outputs when inputs known
  ap_no_x_sub:     assert property (@(x or b) (!$isunknown({x,b})) |-> !$isunknown({b0,b1,b2,b3,b4,b5,b6,b7}));

  // coverage
  cp_x0:           cover  property (@(x) !x);
  cp_x1:           cover  property (@(x)  x);
  cp_b15_one:      cover  property (@(x or b) x && b[15] && (b5==3'b001));
endmodule

bind mul_bodec_16bit mul_bodec_16bit_sva mul_bodec_16bit_sva_i();