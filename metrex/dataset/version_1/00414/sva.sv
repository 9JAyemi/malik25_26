// SVA checker for acl_fp_convert_to_half
// Bind this checker to the DUT:
//   bind acl_fp_convert_to_half acl_fp_convert_to_half_sva #(.HIGH_CAPACITY(HIGH_CAPACITY), .ROUNDING_MODE(ROUNDING_MODE)) u_sva();

module acl_fp_convert_to_half_sva #(parameter int HIGH_CAPACITY = 1,
                                    parameter int ROUNDING_MODE = 0) ();

  // These identifiers resolve in the bound DUT scope
  // DUT ports/regs/wires referenced directly:
  // clock, resetn, dataa, result, valid_in, valid_out, stall_in, stall_out, enable
  // c1_enable, c1_valid, c1_stall, c1_exponent, c1_mantissa, c1_sign
  // c2_enable, c2_valid, c2_stall, c2_exponent, c2_mantissa, c2_sign, c2_temp_mantissa

  default clocking cb @(posedge clock); endclocking
  default disable iff (!resetn)

  // ---------------------------
  // Handshake/control equalities
  // ---------------------------
  generate
    if (HIGH_CAPACITY == 1) begin
      assert property (c1_enable == (~c1_valid | ~c1_stall));
      assert property (c2_enable == (~c2_valid | ~c2_stall));
    end else begin
      assert property (c1_enable == enable);
      assert property (c2_enable == enable);
    end
  endgenerate

  assert property (stall_out == (c1_valid & c1_stall));
  assert property (c1_stall == (c2_valid & c2_stall));
  assert property (c2_stall == stall_in);
  assert property (valid_out == c2_valid);
  assert property (result == {c2_sign, c2_exponent, c2_mantissa});

  // ---------------------------
  // Stability when disabled / stalled
  // ---------------------------
  assert property (!c1_enable |=> $stable({c1_valid, c1_sign, c1_exponent, c1_mantissa}));
  assert property (!c2_enable |=> $stable({c2_valid, c2_sign, c2_exponent, c2_mantissa}));

  // One-step retention under backpressure
  assert property ((c1_valid && c1_stall) |=> c1_valid && $stable({c1_sign, c1_exponent, c1_mantissa}));
  assert property ((c2_valid && c2_stall) |=> c2_valid && $stable({c2_sign, c2_exponent, c2_mantissa}));

  // No X on result when valid
  assert property (valid_out |-> !$isunknown(result));

  // ---------------------------
  // Stage-1 register updates
  // ---------------------------
  // Valid/sign capture
  assert property (c1_enable |=> c1_valid == $past(valid_in));
  assert property (c1_enable |=> c1_sign  == $past(dataa[31]));

  // Underflow/subnormal/zero path
  assert property (c1_enable && ({1'b0, dataa[30:23]} <= 9'd112) |=> c1_exponent == 5'd0);

  // Inf/NaN path
  assert property (c1_enable && (&dataa[30:23]) |=> (c1_exponent == 5'h1f));
  assert property (c1_enable && (&dataa[30:23]) |=> (c1_mantissa[13] == 1'b1 &&
                                                     c1_mantissa[12] == |$past(dataa[22:0]) &&
                                                     c1_mantissa[11:0] == 12'd0));

  // Overflow-to-half range
  generate
    if (ROUNDING_MODE == 0 || ROUNDING_MODE == 1) begin : g_ovf_rtz_rne_sat
      assert property (c1_enable && ({1'b0, dataa[30:23]} > 9'h08e) |=> (c1_exponent == 5'h1f && c1_mantissa == 14'd0));
    end else if (ROUNDING_MODE == 2) begin : g_ovf_trunc
      assert property (c1_enable && ({1'b0, dataa[30:23]} > 9'h08e) |=> (c1_exponent == 5'h1e && c1_mantissa == 14'h3ff8));
    end else if (ROUNDING_MODE == 3) begin : g_ovf_rup
      assert property (c1_enable && ({1'b0, dataa[30:23]} > 9'h08e) && ($past(dataa[31])==1'b0)
                       |=> (c1_exponent == 5'h1f && c1_mantissa == 14'd0));
      assert property (c1_enable && ({1'b0, dataa[30:23]} > 9'h08e) && ($past(dataa[31])==1'b1)
                       |=> (c1_exponent == 5'h1e && c1_mantissa == 14'h3ff8));
    end else if (ROUNDING_MODE == 4) begin : g_ovf_rdn
      assert property (c1_enable && ({1'b0, dataa[30:23]} > 9'h08e) && ($past(dataa[31])==1'b0)
                       |=> (c1_exponent == 5'h1e && c1_mantissa == 14'h3ff8));
      assert property (c1_enable && ({1'b0, dataa[30:23]} > 9'h08e) && ($past(dataa[31])==1'b1)
                       |=> (c1_exponent == 5'h1f && c1_mantissa == 14'd0));
    end
  endgenerate

  // Normalized path (no underflow, no Inf/NaN, no overflow)
  assert property (c1_enable &&
                   !(&dataa[30:23]) &&
                   ({1'b0, dataa[30:23]} > 9'd112) &&
                   ({1'b0, dataa[30:23]} <= 9'h08e)
                   |=> (c1_exponent == ($past(dataa[30:23]) - 8'h70) &&
                        c1_mantissa == {1'b1, $past(dataa[22:11]), |$past(dataa[10:0])}));

  // ---------------------------
  // Stage-2 register updates (round/pack)
  // ---------------------------
  // Valid/sign propagation
  assert property (c2_enable |=> c2_valid == $past(c1_valid));
  assert property (c2_enable |=> c2_sign  == $past(c1_sign));

  // Exponent/mantissa update logic
  assert property (c2_enable && $past(c2_temp_mantissa[11])
                   |=> (c2_exponent == ($past(c1_exponent) + 5'd1) &&
                        c2_mantissa == $past(c2_temp_mantissa[10:1])));

  assert property (c2_enable && !$past(c2_temp_mantissa[11])
                   |=> (c2_exponent == ($past(c1_exponent) + {4'd0, ($past(c2_temp_mantissa[10]) & (~|$past(c1_exponent)))}) &&
                        c2_mantissa == $past(c2_temp_mantissa[9:0])));

  // Quick latency/sign check for a clean 2-stage pass (no internal stalls across boundary)
  assert property ((c1_enable && valid_in) ##1 c2_enable
                   |-> (valid_out && result[15] == $past(dataa[31])));

  // ---------------------------
  // Functional coverage
  // ---------------------------
  // Handshake/stall behavior
  cover property (valid_in ##1 stall_in ##1 stall_in ##1 !stall_in ##1 valid_out);

  // Underflow map coverage across a few exponents in the case statement
  cover property (c1_enable && ($past({1'b0, dataa[30:23]}) <= 9'd112) && $past(dataa[30:23]) == 8'h70);
  cover property (c1_enable && ($past({1'b0, dataa[30:23]}) <= 9'd112) && $past(dataa[30:23]) == 8'h6F);
  cover property (c1_enable && ($past({1'b0, dataa[30:23]}) <= 9'd112) && $past(dataa[30:23]) == 8'h66);
  cover property (c1_enable && ($past({1'b0, dataa[30:23]}) <= 9'd112) &&
                  !$past(dataa[30:23] inside {8'h70,8'h6F,8'h6E,8'h6D,8'h6C,8'h6B,8'h6A,8'h69,8'h68,8'h67,8'h66}));

  // Inf/NaN coverage
  cover property (c1_enable && (&$past(dataa[30:23])) && ($past(|dataa[22:0])==1)); // NaN
  cover property (c1_enable && (&$past(dataa[30:23])) && ($past(|dataa[22:0])==0)); // Inf

  // Overflow coverage (mode-specific)
  cover property (c1_enable && ($past({1'b0, dataa[30:23]}) > 9'h08e));

  // Normalized coverage
  cover property (c1_enable &&
                  !(&$past(dataa[30:23])) &&
                  ($past({1'b0, dataa[30:23]}) > 9'd112) &&
                  ($past({1'b0, dataa[30:23]}) <= 9'h08e));

  // Rounding carry coverage
  cover property (c2_enable && $past(c2_temp_mantissa[11]));
  cover property (c2_enable && !$past(c2_temp_mantissa[11]) && $past(c2_temp_mantissa[10]) && ($past(c1_exponent)==5'd0));

endmodule