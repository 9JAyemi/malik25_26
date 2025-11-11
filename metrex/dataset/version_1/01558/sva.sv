// SVA for module dac
module dac_sva;
  default clocking cb @(posedge clkin); endclocking

  // start after first clock to avoid $past X
  logic started;
  initial started = 1'b0;
  always_ff @(posedge clkin) started <= 1'b1;
  default disable iff (!started);

  localparam int unsigned INT_INC = 122500;
  localparam int unsigned INT_MOD = 59501439;
  localparam int unsigned INT_TH  = 59378938;

  // Basic counter and derived clocks
  assert property (cnt == $past(cnt) + 1);
  assert property (mclk == cnt[2]);
  assert property (lrck == cnt[8]);
  assert property (sclk == cnt[3]);

  // Synchronizer shift behavior
  assert property (sysclk_sreg == { $past(sysclk_sreg[1:0]), $past(sysclk) });
  assert property (sclk_sreg   == { $past(sclk_sreg[1:0]),   $past(sclk)   });
  assert property (lrck_sreg   == { $past(lrck_sreg[1:0]),   $past(lrck)   });
  assert property (reset_sreg  == { $past(reset_sreg[0]),    $past(reset)  });

  // Simple mappings
  assert property (DAC_STATUS == dac_address_r[8]);
  assert property (dac_address == dac_address_r);
  assert property (sdout == sdout_reg);
  assert property (play_r == $past(play));

  // Reset effects
  assert property (reset_rising |=> (interpol_count == 0 && dac_address_r == 0));

  // Interpolator hold when not enabled
  assert property (!reset_rising && !sysclk_rising |=> $stable(interpol_count) && $stable(dac_address_r));

  // Interpolator advance - no wrap
  assert property (sysclk_rising && !(interpol_count > INT_TH) |=> 
                   interpol_count == $past(interpol_count) + INT_INC &&
                   dac_address_r  == $past(dac_address_r));

  // Interpolator advance - wrap and address step with play_r
  assert property (sysclk_rising && (interpol_count > INT_TH) |=> 
                   interpol_count == $past(interpol_count) + INT_INC - INT_MOD &&
                   dac_address_r  == $past(dac_address_r) + $past(play_r));

  // Channel load on LRCK edges
  assert property (lrck_rising  |=> smpshift == (({16'h0, dac_data[31:16]} * vol_reg) >> 8));
  assert property (lrck_falling |=> smpshift == (({16'h0, dac_data[15:0]}  * vol_reg) >> 8));

  // Shift-out on SCLK rising when not (re)loading
  assert property (sclk_rising && !lrck_rising && !lrck_falling |=> 
                   smpcnt      == $past(smpcnt) + 16'd1 &&
                   sdout_reg   == $past(smpshift[15]) &&
                   smpshift    == { $past(smpshift[14:0]), 1'b0 });

  // smpcnt holds otherwise
  assert property (!(sclk_rising && !lrck_rising && !lrck_falling) |=> $stable(smpcnt));

  // samples counter behavior
  assert property (lrck_rising |=> samples == $past(samples) + 2'd1);
  assert property (!lrck_rising |=> $stable(samples));

  // Volume ramp behavior (only when lrck_rising and samples==2'b11)
  assert property ((lrck_rising && &samples) && (vol_reg > vol_target_reg) |=> vol_reg == $past(vol_reg) - 8'd1);
  assert property ((lrck_rising && &samples) && (vol_reg < vol_target_reg) |=> vol_reg == $past(vol_reg) + 8'd1);
  assert property ((lrck_rising && &samples) && (vol_reg == vol_target_reg) |=> $stable(vol_reg));
  assert property (!(lrck_rising && &samples) |=> $stable(vol_reg));

  // Coverage
  cover property (lrck_rising ##1 lrck_falling);
  cover property (sysclk_rising && (interpol_count > INT_TH));
  cover property ((lrck_rising && &samples) && (vol_reg < vol_target_reg));
  cover property ((lrck_rising && &samples) && (vol_reg > vol_target_reg));

  // 16 SCLK rising edges per LRCK half-period
  sequence sclk16; (sclk_rising && !lrck_rising && !lrck_falling) [->16]; endsequence
  cover property (lrck_rising  ##1 sclk16 ##1 lrck_falling);
  cover property (lrck_falling ##1 sclk16 ##1 lrck_rising);
endmodule

bind dac dac_sva dac_sva_i();