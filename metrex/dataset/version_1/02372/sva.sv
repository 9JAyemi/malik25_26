// SVA for jt10_adpcm_dt
// Bind into the DUT to access internal signals directly.
module jt10_adpcm_dt_sva;

  // Clocking/disable
  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Reset value checks (asynchronous reset active)
  // Use an immediate assertion style to check values when reset is asserted.
  always @(posedge clk) if (!rst_n) begin
    assert (x1==16'sd0 && x2==16'sd0 && x3==16'sd0 && x4==16'sd0 && x5==16'sd0 && x6==16'sd0);
    assert (step1==15'd127 && step2==15'd127 && step3==15'd127 && step4==15'd127 && step5==15'd127 && step6==15'd127);
    assert (d2==4'd0 && d3==16'd0 && d4==16'd0);
    assert (!sign2 && !sign3 && !sign4 && !sign5);
    assert (!chon2 && !chon3 && !chon4 && !chon5);
  end

  // When cen=0, all flops hold
  ap_hold_on_cen0: assert property (!cen |-> $stable({
      x1,x2,x3,x4,x5,x6,
      step1,step2,step3,step4,step5,step6,
      d2,d3,d4,
      sign2,sign3,sign4,sign5,
      chon2,chon3,chon4,chon5,
      signEqu4,signEqu5,
      data2
  }));

  // Combinational relations sampled on clk
  ap_d2l_mul:    assert (d2l    == d2 * step2);
  ap_step2l_mul: assert (step2l == step_val * step2);

  // step_val decode (casez)
  ap_stepval_0xx: assert ((d2[3]==1'b0)                     |-> (step_val==8'd57));
  ap_stepval_100: assert ((d2[3:1]==3'b100)                 |-> (step_val==8'd77));
  ap_stepval_101: assert ((d2[3:1]==3'b101)                 |-> (step_val==8'd102));
  ap_stepval_110: assert ((d2[3:1]==3'b110)                 |-> (step_val==8'd128));
  ap_stepval_111: assert ((d2[3:1]==3'b111)                 |-> (step_val==8'd153));

  // Stage 1 updates (1-cycle latency under cen)
  ap_s1: assert property (cen |-> ##1 (
      d2    == $past({data[2:0],1'b1}) &&
      sign2 == $past(data[3]) &&
      data2 == $past(data) &&
      x2    == $past(x1) &&
      step2 == $past(step1) &&
      chon2 == $past(chon)
  ));

  // Stage 2
  ap_s2: assert property (cen |-> ##1 (
      d3    == $past(d2l[18:3]) &&
      sign3 == $past(sign2) &&
      x3    == $past(x2) &&
      step3 == $past(step2l[22:6]) &&
      chon3 == $past(chon2)
  ));

  // Stage 3
  ap_s3: assert property (cen |-> ##1 (
      d4       == $past( sign3 ? (~d3 + 16'b1) : d3 ) &&
      sign4    == $past(sign3) &&
      signEqu4 == ($past(sign3) == $past(x3[15])) &&
      x4       == $past(x3) &&
      step4    == $past(step3) &&
      chon4    == $past(chon3)
  ));

  // Stage 4
  ap_s4: assert property (cen |-> ##1 (
      x5       == $past(x4) + $signed($past(d4)) &&
      sign5    == $past(sign4) &&
      signEqu5 == $past(signEqu4) &&
      step5    == $past(step4) &&
      chon5    == $past(chon4)
  ));

  // Stage 5 (active): saturation vs pass-through
  ap_s5_sat_pos: assert property (cen && $past(chon5) &&  $past(signEqu5) && ($past(sign5)==1'b0) && ($past(x5[15])==1'b1) |-> ##1 (x6==16'sh7FFF));
  ap_s5_sat_neg: assert property (cen && $past(chon5) &&  $past(signEqu5) && ($past(sign5)==1'b1) && ($past(x5[15])==1'b0) |-> ##1 (x6==16'sh8000));
  ap_s5_passth:  assert property (cen && $past(chon5) && !( $past(signEqu5) && ($past(sign5) != $past(x5[15])) )         |-> ##1 (x6==$past(x5)));

  // Stage 5 (active): step clamp
  ap_s5_step_lo: assert property (cen && $past(chon5) && ($past(step5) <  15'd127)   |-> ##1 (step6==15'd127));
  ap_s5_step_hi: assert property (cen && $past(chon5) && ($past(step5) >  15'd24576) |-> ##1 (step6==15'd24576));
  ap_s5_step_ok: assert property (cen && $past(chon5) && ($past(step5) >= 15'd127) && ($past(step5) <= 15'd24576) |-> ##1 (step6==$past(step5[14:0])));

  // Stage 5 (idle)
  ap_s5_idle: assert property (cen && !$past(chon5) |-> ##1 (x6==16'sd0 && step6==15'd127));

  // Stage 6 feedback
  ap_s6_fb: assert property (cen |-> ##1 (x1==$past(x6) && step1==$past(step6)));

  // Output mapping
  ap_pcm_map: assert (pcm==x2);

  // Coverage

  // Exercise all step_val decode cases
  cv_stepval_0xx: cover property (rst_n && cen && (d2[3]==1'b0)                     && (step_val==8'd57));
  cv_stepval_100: cover property (rst_n && cen && (d2[3:1]==3'b100)                 && (step_val==8'd77));
  cv_stepval_101: cover property (rst_n && cen && (d2[3:1]==3'b101)                 && (step_val==8'd102));
  cv_stepval_110: cover property (rst_n && cen && (d2[3:1]==3'b110)                 && (step_val==8'd128));
  cv_stepval_111: cover property (rst_n && cen && (d2[3:1]==3'b111)                 && (step_val==8'd153));

  // Saturation cover (both directions)
  cv_sat_pos: cover property (cen && $past(chon5) && $past(signEqu5) && ($past(sign5)==1'b0) && ($past(x5[15])==1'b1) ##1 (x6==16'sh7FFF));
  cv_sat_neg: cover property (cen && $past(chon5) && $past(signEqu5) && ($past(sign5)==1'b1) && ($past(x5[15])==1'b0) ##1 (x6==16'sh8000));

  // Step clamp cover (low, high, passthrough)
  cv_step_lo:  cover property (cen && $past(chon5) && ($past(step5) <  15'd127)   ##1 (step6==15'd127));
  cv_step_hi:  cover property (cen && $past(chon5) && ($past(step5) >  15'd24576) ##1 (step6==15'd24576));
  cv_step_mid: cover property (cen && $past(chon5) && ($past(step5) >= 15'd127) && ($past(step5) <= 15'd24576) ##1 (step6==$past(step5[14:0])));

  // Full active pipeline burst (6 cen cycles with chon active reaching x6)
  sequence six_cen; cen ##1 cen ##1 cen ##1 cen ##1 cen ##1 cen; endsequence
  cv_full_path: cover property (rst_n && six_cen and $past(chon,5));

endmodule

bind jt10_adpcm_dt jt10_adpcm_dt_sva sva_i();