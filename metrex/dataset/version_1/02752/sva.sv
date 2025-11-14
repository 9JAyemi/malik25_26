// SVA for acl_fp_convert_from_long
// Bind this module to the DUT: bind acl_fp_convert_from_long acl_fp_convert_from_long_sva sva();

module acl_fp_convert_from_long_sva (acl_fp_convert_from_long dut);

  // Basic interface equivalences
  assert property (@(posedge dut.clock) disable iff (!dut.resetn)
                   dut.valid_out == dut.c5_valid);
  assert property (@(posedge dut.clock) disable iff (!dut.resetn)
                   dut.result == {dut.c5_sign, dut.c5_exponent, dut.c5_mantissa});
  assert property (@(posedge dut.clock) disable iff (!dut.resetn)
                   dut.stall_out == (dut.c1_valid & dut.c1_stall));

  // Stall chain equivalences
  assert property (@(posedge dut.clock) disable iff (!dut.resetn)
                   dut.c1_stall == (dut.c2_valid & dut.c2_stall));
  assert property (@(posedge dut.clock) disable iff (!dut.resetn)
                   dut.c2_stall == (dut.c3_valid & dut.c3_stall));
  assert property (@(posedge dut.clock) disable iff (!dut.resetn)
                   dut.c3_stall == (dut.c4_valid & dut.c4_stall));
  assert property (@(posedge dut.clock) disable iff (!dut.resetn)
                   dut.c4_stall == (dut.c5_valid & dut.c5_stall));
  assert property (@(posedge dut.clock) disable iff (!dut.resetn)
                   dut.c5_stall == dut.stall_in);

  // Enable policy
  assert property (@(posedge dut.clock) disable iff (!dut.resetn)
                   (dut.HIGH_CAPACITY==1) |-> (dut.c1_enable == (~dut.c1_valid | ~dut.c1_stall)));
  assert property (@(posedge dut.clock) disable iff (!dut.resetn)
                   (dut.HIGH_CAPACITY==1) |-> (dut.c2_enable == (~dut.c2_valid | ~dut.c2_stall)));
  assert property (@(posedge dut.clock) disable iff (!dut.resetn)
                   (dut.HIGH_CAPACITY==1) |-> (dut.c3_enable == (~dut.c3_valid | ~dut.c3_stall)));
  assert property (@(posedge dut.clock) disable iff (!dut.resetn)
                   (dut.HIGH_CAPACITY==1) |-> (dut.c4_enable == (~dut.c4_valid | ~dut.c4_stall)));
  assert property (@(posedge dut.clock) disable iff (!dut.resetn)
                   (dut.HIGH_CAPACITY==1) |-> (dut.c5_enable == (~dut.c5_valid | ~dut.c5_stall)));
  assert property (@(posedge dut.clock) disable iff (!dut.resetn)
                   (dut.HIGH_CAPACITY==0) |-> (dut.c1_enable==dut.enable && dut.c2_enable==dut.enable &&
                                               dut.c3_enable==dut.enable && dut.c4_enable==dut.enable &&
                                               dut.c5_enable==dut.enable));

  // Hold-on-stall behavior (HIGH_CAPACITY)
  assert property (@(posedge dut.clock) disable iff (!dut.resetn)
                   (dut.HIGH_CAPACITY && dut.c1_valid && dut.c1_stall) |-> (!dut.c1_enable && $stable({dut.c1_valid,dut.c1_sign,dut.c1_value_to_convert})));
  assert property (@(posedge dut.clock) disable iff (!dut.resetn)
                   (dut.HIGH_CAPACITY && dut.c2_valid && dut.c2_stall) |-> (!dut.c2_enable && $stable({dut.c2_valid,dut.c2_sign,dut.c2_done,dut.c2_exponent,dut.c2_value_to_convert})));
  assert property (@(posedge dut.clock) disable iff (!dut.resetn)
                   (dut.HIGH_CAPACITY && dut.c3_valid && dut.c3_stall) |-> (!dut.c3_enable && $stable({dut.c3_valid,dut.c3_sign,dut.c3_done,dut.c3_exponent,dut.c3_value_to_convert})));
  assert property (@(posedge dut.clock) disable iff (!dut.resetn)
                   (dut.HIGH_CAPACITY && dut.c4_valid && dut.c4_stall) |-> (!dut.c4_enable && $stable({dut.c4_valid,dut.c4_sign,dut.c4_exponent,dut.c4_value_to_convert})));
  assert property (@(posedge dut.clock) disable iff (!dut.resetn)
                   (dut.HIGH_CAPACITY && dut.c5_valid && dut.c5_stall) |-> (!dut.c5_enable && $stable({dut.c5_valid,dut.c5_sign,dut.c5_exponent,dut.c5_mantissa})));

  // Valid propagation when stage enabled
  assert property (@(posedge dut.clock) disable iff (!dut.resetn)
                   dut.c2_enable |-> ##1 (dut.c2_valid == $past(dut.c1_valid)));
  assert property (@(posedge dut.clock) disable iff (!dut.resetn)
                   dut.c3_enable |-> ##1 (dut.c3_valid == $past(dut.c2_valid)));
  assert property (@(posedge dut.clock) disable iff (!dut.resetn)
                   dut.c4_enable |-> ##1 (dut.c4_valid == $past(dut.c3_valid)));
  assert property (@(posedge dut.clock) disable iff (!dut.resetn)
                   dut.c5_enable |-> ##1 (dut.c5_valid == $past(dut.c4_valid)));

  // Stage-1 capture: sign and magnitude
  assert property (@(posedge dut.clock) disable iff (!dut.resetn)
                   dut.c1_enable |-> ##1 (dut.c1_valid == $past(dut.valid_in)));
  assert property (@(posedge dut.clock) disable iff (!dut.resetn)
                   (dut.c1_enable && dut.UNSIGNED==1) |-> ##1 (dut.c1_sign==1'b0 && dut.c1_value_to_convert==$past(dut.dataa)));
  assert property (@(posedge dut.clock) disable iff (!dut.resetn)
                   (dut.c1_enable && dut.UNSIGNED==0) |-> ##1 (dut.c1_sign==$past(dut.dataa[63]) &&
                                                                dut.c1_value_to_convert == (($past(dut.dataa) ^ {64{$past(dut.dataa[63])}}) + {1'b0,$past(dut.dataa[63])})));

  // Stage-2: done, exponent init, shift
  assert property (@(posedge dut.clock) disable iff (!dut.resetn)
                   dut.c2_enable |-> ##1 (dut.c2_sign==$past(dut.c1_sign)));
  assert property (@(posedge dut.clock) disable iff (!dut.resetn)
                   dut.c2_enable |-> ##1 (dut.c2_done == (~(|$past(dut.c1_value_to_convert[63:32])) & ~(|$past(dut.c1_value_to_convert[31:0])))));
  // If done -> exponent=0, no shift
  assert property (@(posedge dut.clock) disable iff (!dut.resetn)
                   (dut.c2_enable && (~(|$past(dut.c1_value_to_convert[63:32])) & ~(|$past(dut.c1_value_to_convert[31:0]))))
                   |-> ##1 (dut.c2_exponent==8'd0 && dut.c2_value_to_convert==$past(dut.c1_value_to_convert)));
  // If not done -> exponent and shifted value per c2_shift_value
  assert property (@(posedge dut.clock) disable iff (!dut.resetn)
                   (dut.c2_enable && ~((~(|$past(dut.c1_value_to_convert[63:32])) & ~(|$past(dut.c1_value_to_convert[31:0])))))
                   |-> ##1 (dut.c2_exponent == (8'd190 - {1'b0,$past(dut.c2_shift_value),4'd0})));
  assert property (@(posedge dut.clock) disable iff (!dut.resetn)
                   (dut.c2_enable && $past(dut.c2_shift_value)==2'b11) |-> ##1 (dut.c2_value_to_convert == { $past(dut.c1_value_to_convert[15:0]), 48'd0 }));
  assert property (@(posedge dut.clock) disable iff (!dut.resetn)
                   (dut.c2_enable && $past(dut.c2_shift_value)==2'b10) |-> ##1 (dut.c2_value_to_convert == { $past(dut.c1_value_to_convert[31:0]), 32'd0 }));
  assert property (@(posedge dut.clock) disable iff (!dut.resetn)
                   (dut.c2_enable && $past(dut.c2_shift_value)==2'b01) |-> ##1 (dut.c2_value_to_convert == { $past(dut.c1_value_to_convert[47:0]), 16'd0 }));
  assert property (@(posedge dut.clock) disable iff (!dut.resetn)
                   (dut.c2_enable && $past(dut.c2_shift_value)==2'b00) |-> ##1 (dut.c2_value_to_convert == $past(dut.c1_value_to_convert)));

  // Stage-3: exponent adjust and shift, done/sign propagate
  assert property (@(posedge dut.clock) disable iff (!dut.resetn)
                   dut.c3_enable |-> ##1 (dut.c3_done==$past(dut.c2_done) && dut.c3_sign==$past(dut.c2_sign)));
  assert property (@(posedge dut.clock) disable iff (!dut.resetn)
                   dut.c3_enable |-> ##1 (dut.c3_exponent == ($past(dut.c2_exponent) - {1'b0,$past(dut.c3_exp_adjust),2'd0})));
  assert property (@(posedge dut.clock) disable iff (!dut.resetn)
                   (dut.c3_enable && $past(dut.c3_exp_adjust)==2'b11) |-> ##1 (dut.c3_value_to_convert == { $past(dut.c2_value_to_convert[51:0]), 12'd0 }));
  assert property (@(posedge dut.clock) disable iff (!dut.resetn)
                   (dut.c3_enable && $past(dut.c3_exp_adjust)==2'b10) |-> ##1 (dut.c3_value_to_convert == { $past(dut.c2_value_to_convert[55:0]), 8'd0 }));
  assert property (@(posedge dut.clock) disable iff (!dut.resetn)
                   (dut.c3_enable && $past(dut.c3_exp_adjust)==2'b01) |-> ##1 (dut.c3_value_to_convert == { $past(dut.c2_value_to_convert[59:0]), 4'd0 }));
  assert property (@(posedge dut.clock) disable iff (!dut.resetn)
                   (dut.c3_enable && $past(dut.c3_exp_adjust)==2'b00) |-> ##1 (dut.c3_value_to_convert == $past(dut.c2_value_to_convert)));

  // Stage-4: exponent adjust and shift, sign propagate
  assert property (@(posedge dut.clock) disable iff (!dut.resetn)
                   dut.c4_enable |-> ##1 (dut.c4_sign==$past(dut.c3_sign)));
  assert property (@(posedge dut.clock) disable iff (!dut.resetn)
                   dut.c4_enable |-> ##1 (dut.c4_exponent == ($past(dut.c3_exponent) - {1'b0,$past(dut.c4_exp_adjust)})));
  assert property (@(posedge dut.clock) disable iff (!dut.resetn)
                   (dut.c4_enable && $past(dut.c4_exp_adjust)==2'b11) |-> ##1 (dut.c4_value_to_convert == { $past(dut.c3_value_to_convert[60:0]), 3'd0 }));
  assert property (@(posedge dut.clock) disable iff (!dut.resetn)
                   (dut.c4_enable && $past(dut.c4_exp_adjust)==2'b10) |-> ##1 (dut.c4_value_to_convert == { $past(dut.c3_value_to_convert[61:0]), 2'd0 }));
  assert property (@(posedge dut.clock) disable iff (!dut.resetn)
                   (dut.c4_enable && $past(dut.c4_exp_adjust)==2'b01) |-> ##1 (dut.c4_value_to_convert == { $past(dut.c3_value_to_convert[62:0]), 1'd0 }));
  assert property (@(posedge dut.clock) disable iff (!dut.resetn)
                   (dut.c4_enable && $past(dut.c4_exp_adjust)==2'b00) |-> ##1 (dut.c4_value_to_convert == $past(dut.c3_value_to_convert)));

  // Stage-5: rounding pack
  assert property (@(posedge dut.clock) disable iff (!dut.resetn)
                   dut.c5_enable |-> ##1 (dut.c5_sign==$past(dut.c4_sign)));
  assert property (@(posedge dut.clock) disable iff (!dut.resetn)
                   dut.c5_enable |-> ##1 (dut.c5_exponent == ($past(dut.c4_exponent) + $past(dut.c5_temp_mantissa[24]))));
  assert property (@(posedge dut.clock) disable iff (!dut.resetn)
                   dut.c5_enable |-> ##1 (dut.c5_mantissa == ($past(dut.c5_temp_mantissa[24]) ? $past(dut.c5_temp_mantissa[23:1]) : $past(dut.c5_temp_mantissa[22:0]))));

  // Zero-input end-to-end: result must be zero (sign=0, exp=0, mantissa=0)
  assert property (@(posedge dut.clock) disable iff (!dut.resetn)
                   (dut.c1_enable && $past(dut.valid_in) && $past(dut.dataa)==64'd0)
                   |-> ##[4:$] (dut.valid_out && dut.result==32'd0));

  // --------------- Coverage ---------------

  // Transaction gets through to output eventually
  cover property (@(posedge dut.clock) disable iff (!dut.resetn)
                  (dut.valid_in && dut.c1_enable) ##[1:$] dut.valid_out);

  // Backpressure propagates to all stages (HC only)
  cover property (@(posedge dut.clock) disable iff (!dut.resetn)
                  (dut.HIGH_CAPACITY && dut.valid_out && dut.stall_in)
                  ##1 (dut.c4_stall && dut.c3_stall && dut.c2_stall && dut.c1_stall));

  // Rounding carry generated
  cover property (@(posedge dut.clock) disable iff (!dut.resetn)
                  (dut.c5_enable && dut.c5_temp_mantissa[24]));
  // No rounding carry
  cover property (@(posedge dut.clock) disable iff (!dut.resetn)
                  (dut.c5_enable && !dut.c5_temp_mantissa[24]));

  // Shift patterns exercised in c2
  cover property (@(posedge dut.clock) disable iff (!dut.resetn)
                  (dut.c2_enable && $past(dut.c2_shift_value)==2'b00));
  cover property (@(posedge dut.clock) disable iff (!dut.resetn)
                  (dut.c2_enable && $past(dut.c2_shift_value)==2'b01));
  cover property (@(posedge dut.clock) disable iff (!dut.resetn)
                  (dut.c2_enable && $past(dut.c2_shift_value)==2'b10));
  cover property (@(posedge dut.clock) disable iff (!dut.resetn)
                  (dut.c2_enable && $past(dut.c2_shift_value)==2'b11));

  // Shift patterns exercised in c3/c4
  cover property (@(posedge dut.clock) disable iff (!dut.resetn)
                  (dut.c3_enable && $past(dut.c3_exp_adjust)==2'b00));
  cover property (@(posedge dut.clock) disable iff (!dut.resetn)
                  (dut.c3_enable && $past(dut.c3_exp_adjust)==2'b01));
  cover property (@(posedge dut.clock) disable iff (!dut.resetn)
                  (dut.c3_enable && $past(dut.c3_exp_adjust)==2'b10));
  cover property (@(posedge dut.clock) disable iff (!dut.resetn)
                  (dut.c3_enable && $past(dut.c3_exp_adjust)==2'b11));
  cover property (@(posedge dut.clock) disable iff (!dut.resetn)
                  (dut.c4_enable && $past(dut.c4_exp_adjust)==2'b00));
  cover property (@(posedge dut.clock) disable iff (!dut.resetn)
                  (dut.c4_enable && $past(dut.c4_exp_adjust)==2'b01));
  cover property (@(posedge dut.clock) disable iff (!dut.resetn)
                  (dut.c4_enable && $past(dut.c4_exp_adjust)==2'b10));
  cover property (@(posedge dut.clock) disable iff (!dut.resetn)
                  (dut.c4_enable && $past(dut.c4_exp_adjust)==2'b11));

  // Signed negative path (only when signed)
  cover property (@(posedge dut.clock) disable iff (!dut.resetn)
                  (dut.UNSIGNED==0 && dut.c1_enable && $past(dut.dataa[63])));

  // Zero input path
  cover property (@(posedge dut.clock) disable iff (!dut.resetn)
                  (dut.c1_enable && $past(dut.dataa)==64'd0));

endmodule

// Bind example (instantiate per DUT instance or type):
// bind acl_fp_convert_from_long acl_fp_convert_from_long_sva sva();