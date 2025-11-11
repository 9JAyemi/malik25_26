// SVA for multiplier_block
// Bind into the DUT to check internal relationships and end-to-end behavior.

module multiplier_block_sva;

  // Structural equivalence of every wire (combinational settle via ##0)
  ap_w1:       assert property (@(*) ##0 (w1       == i_data0));
  ap_w4:       assert property (@(*) ##0 (w4       == (w1 << 2)));
  ap_w5:       assert property (@(*) ##0 (w5       == (w1 + w4)));
  ap_w8192:    assert property (@(*) ##0 (w8192    == (w1 << 13)));
  ap_w8187:    assert property (@(*) ##0 (w8187    == (w8192 - w5)));
  ap_w160:     assert property (@(*) ##0 (w160     == (w5 << 5)));
  ap_w8027:    assert property (@(*) ##0 (w8027    == (w8187 - w160)));
  ap_w16054:   assert property (@(*) ##0 (w16054   == (w8027 << 1)));
  ap_out_wire: assert property (@(*) ##0 (o_data0  == w16054));

  // End-to-end functional equivalence: o = (16054 * i) mod 2^32
  ap_const_mult: assert property (@(*) ##0 (o_data0 == (i_data0 * 32'd16054)[31:0]));

  // X-propagation guarantee: if input is known, output must be known
  ap_known: assert property (@(*) (!$isunknown(i_data0)) |-> ##0 (!$isunknown(o_data0)));

  // Targeted functional coverage
  cp_nonzero:           cover property (@(*) ##0 (i_data0 != 32'd0));
  cp_one:               cover property (@(*) ##0 (i_data0 == 32'd1));
  cp_max:               cover property (@(*) ##0 (i_data0 == 32'hFFFF_FFFF));
  cp_msb_set:           cover property (@(*) ##0 (i_data0[31]));
  cp_shift2_overflow:   cover property (@(*) ##0 (|i_data0[31:30])); // bits lost in <<2
  cp_shift5_overflow:   cover property (@(*) ##0 (|i_data0[31:27])); // bits lost in <<5
  cp_shift13_overflow:  cover property (@(*) ##0 (|i_data0[31:19])); // bits lost in <<13
  cp_add_overflow:      cover property (@(*) ##0 (w5 < w1));         // w1 + (w1<<2) wrapped
  cp_sub1_underflow:    cover property (@(*) ##0 (w8192 < w5));      // w8192 - w5 underflowed
  cp_sub2_underflow:    cover property (@(*) ##0 (w8187 < w160));    // w8187 - w160 underflowed
  cp_shift1_overflow:   cover property (@(*) ##0 (w8027[31]));       // <<1 overflow before final

endmodule

bind multiplier_block multiplier_block_sva mb_sva();