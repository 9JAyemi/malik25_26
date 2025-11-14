// SVA checker for ag6502_phase_shift
module ag6502_phase_shift_sva #(parameter int DELAY = 1)
(
  input logic        baseclk,
  input logic        phi_0,
  input logic        phi_1,
  input int          cnt,
  input logic        delayed_clk
);

  default clocking cb @(posedge baseclk); endclocking

  logic past_valid; initial past_valid = 0;
  always @(cb) past_valid <= 1'b1;

  // Sanity/knowns
  ap_known_io: assert property (@cb !$isunknown({phi_0,phi_1}));
  ap_known_int: assert property (@cb !$isunknown({cnt,delayed_clk}));

  // Counter range and behavior
  ap_cnt_range: assert property (@cb (cnt >= 0) && (cnt <= DELAY));

  ap_cnt_dec: assert property (@cb disable iff(!past_valid)
                               ($past(cnt) > 0) |-> (cnt == $past(cnt)-1));

  ap_cnt_load: assert property (@cb disable iff(!past_valid)
                                ($past(cnt)==0 && $past(phi_0 != phi_1))
                                |-> (cnt==DELAY && delayed_clk==1));

  ap_cnt_idle: assert property (@cb disable iff(!past_valid)
                                ($past(cnt)==0 && $past(phi_0 == phi_1))
                                |-> (cnt==0 && delayed_clk==0));

  ap_busy_dclk: assert property (@cb (cnt>0) |-> (delayed_clk==1));

  // phi_1 update rules (implementation-consistent)
  ap_hold_when_cnt: assert property (@cb (cnt>0) |-> $stable(phi_1));

  ap_toggle_when_gate: assert property (@cb disable iff(!past_valid)
                                        ($past(cnt)==0 && $past(delayed_clk)==1) |-> $changed(phi_1));

  ap_track_when_idle: assert property (@cb disable iff(!past_valid)
                                       ($past(cnt)==0 && $past(delayed_clk)==0) |-> (phi_1==phi_0));

  ap_no_spurious_phi1: assert property (@cb disable iff(!past_valid)
                                        $changed(phi_1) |->
                                        (($past(cnt)==0 && $past(delayed_clk)==1) ||
                                         ($past(cnt)==0 && $past(delayed_clk)==0 && $changed(phi_0))));

  // High-level functional intent: each phi_0 edge causes exactly one phi_1 edge after DELAY cycles
  generate
    if (DELAY > 0) begin
      ap_follow_after_delay: assert property (@cb
        $changed(phi_0) |=> (! $changed(phi_1))[* (DELAY-1)] ##1 $changed(phi_1));

      ap_no_early_phi1: assert property (@cb
        $changed(phi_0) |=> (! $changed(phi_1))[* (DELAY-1)]);
    end else begin : g_delay0
      ap_delay0_track: assert property (@cb phi_1 == phi_0);
    end
  endgenerate

  // Once applied, phi_1 matches phi_0 until next phi_0 change
  ap_equal_after_apply: assert property (@cb disable iff(!past_valid)
    ($past(cnt)==0 && $past(delayed_clk)==1) |-> (phi_1==phi_0));

  ap_no_extra_toggles: assert property (@cb
    $changed(phi_1) |-> (! $changed(phi_1)) until $changed(phi_0));

  // Coverage
  cp_rise:  cover property (@cb $rose(phi_0)  ##[1:DELAY] $rose(phi_1));
  cp_fall:  cover property (@cb $fell(phi_0)  ##[1:DELAY] $fell(phi_1));
  cp_busy_overlap: cover property (@cb (cnt>0) ##1 $changed(phi_0));
  cp_cnt_run: cover property (@cb (cnt==DELAY) ##[1:DELAY] (cnt==0) && delayed_clk);

endmodule

// Bind into DUT (accesses internal cnt and delayed_clk)
bind ag6502_phase_shift
  ag6502_phase_shift_sva #(.DELAY(DELAY)) ag6502_phase_shift_sva_i
  (.baseclk(baseclk), .phi_0(phi_0), .phi_1(phi_1), .cnt(cnt), .delayed_clk(delayed_clk));