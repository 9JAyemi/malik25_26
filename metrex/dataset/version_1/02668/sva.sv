// SVA for module flip_flop
module flip_flop_sva;

  // Access bound instance signals directly (Q, CLK, D, DE, SCD, SCE, VPWR, VGND, VPB, VNB, scan_en, Q_reg)
  default clocking cb @(posedge CLK); endclocking

  bit past_valid;
  initial past_valid = 0;
  always @(posedge CLK) past_valid <= 1;

  // scan_en combinational definition
  a_scan_en_def: assert property (scan_en == (SCE && !SCD));

  // Power/ground rails tied correctly
  a_power_tied:  assert property (VPWR===1'b1 && VPB===1'b1 && VGND===1'b0 && VNB===1'b0);

  // Output function matches combinational spec on all events that can change Q
  a_Q_func_events: assert property (@(posedge CLK or posedge SCE or negedge SCE or posedge SCD or negedge SCD)
                                    Q === (scan_en ? Q_reg : 1'b0));
  // Also sample at clock for robustness
  a_Q_func_clk:    assert property (Q === (scan_en ? Q_reg : 1'b0));

  // Load behavior: on enabled clock, Q_reg captures D; Q follows D next cycle when enabled
  a_load_on_en:          assert property (past_valid && (scan_en && DE) |=> (Q_reg == $past(D)));
  a_Q_follows_D_on_load: assert property (past_valid && (scan_en && DE) |=> (Q     == $past(D)));

  // Hold behavior: when not loading, Q_reg holds its value
  a_hold_when_not_en: assert property (!(scan_en && DE) |=> $stable(Q_reg));

  // When disabled, Q is forced low
  a_Q_zero_when_disabled: assert property (!scan_en |-> (Q==1'b0));

  // When enabled and DE low, Q stays stable across cycles
  a_Q_stable_no_load: assert property (past_valid && $past(scan_en) && scan_en && !$past(DE) |-> (Q == $past(Q)));

  // Sanity: no X on Q when disabled
  a_no_x_when_disabled: assert property (!scan_en |-> !$isunknown(Q));

  // Coverage
  c_load_1:           cover property (past_valid && scan_en && DE && D==1 ##1 Q==1);
  c_load_0:           cover property (past_valid && scan_en && DE && D==0 ##1 Q==0);
  c_disable_toggle:   cover property (!scan_en ##1 scan_en ##1 !scan_en);
  c_zero_when_disabled: cover property (!scan_en ##1 Q==0);

endmodule

bind flip_flop flip_flop_sva sva_inst();