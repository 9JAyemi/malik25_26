// SVA for module pulses
// Bind these assertions to the DUT. Focused on functional correctness,
// CDC-safety (parameters stable within a counter frame), and coverage.

module pulses_sva;

  // Two clock domains in the DUT
  default clocking cb_pll @(posedge clk_pll); endclocking
  clocking        cb_clk @(posedge clk);      endclocking

  // -----------------------------
  // CDC safety: hold all timing/control regs stable during a frame
  // (allow updates only when counter==0)
  // -----------------------------
  ap_params_stable: assert property (cb_pll
    (counter != 0) |-> $stable({period,p1width,p2width,delay,cpmg,block,p2start,sync_down,block_off,cw})
  );

  // -----------------------------
  // Derived-time relations (checked in clk domain)
  // -----------------------------
  ap_derived_defs: assert property (cb_clk
    (p2start   == p1width + delay)
    && (sync_down == ((cpmg > 0) ? (p2start + p2width) : (period << 7)))
    && (block_off == (p2start + p2width + delay - pulse_block))
    && (cw == ((cpmg > 0) ? 1'b0 : 1'b1))
  );

  // Basic sanity on ranges (applies in pll domain where used)
  ap_time_order_cpmg: assert property (cb_pll
    (cpmg > 0) |-> (0 < p1width) && (p1width <= p2start) && (p2start < sync_down) && (sync_down < (period << 8))
  );
  ap_time_order_cw: assert property (cb_pll
    (cw == 1) |-> (sync_down == (period << 7)) && (sync_down < (period << 8))
  );

  // -----------------------------
  // Counter progression/wrap (use previous-period threshold)
  // -----------------------------
  ap_cnt_inc: assert property (cb_pll
    ($past(counter) < ($past(period) << 8)) |-> (counter == $past(counter) + 32'd1)
  );
  ap_cnt_wrap: assert property (cb_pll
    ($past(counter) == ($past(period) << 8)) |-> (counter == 32'd0)
  );

  // -----------------------------
  // Output changes only at legal event times
  // -----------------------------
  ap_pulse_change_when: assert property (cb_pll
    $changed(pulse_on) |-> ((counter==0) || (counter==p1width) || (counter==p2start) || (counter==sync_down))
  );
  ap_sync_change_when: assert property (cb_pll
    $changed(sync_on)  |-> ((counter==0) || (counter==sync_down))
  );
  ap_inh_change_when: assert property (cb_pll
    $changed(inhib)    |-> ((counter==0) || (counter==block_off))
  );

  // -----------------------------
  // Exact drives at event times (guard against aliasing equals)
  // -----------------------------
  ap_init_drive: assert property (cb_pll
    (counter==0) |=> (pulse_on==1'b1 && sync_on==1'b1 && inhib==block)
  );
  ap_p1width_drive: assert property (cb_pll
    (counter==p1width && p1width!=0) |=> (pulse_on==cw)
  );
  ap_p2start_drive: assert property (cb_pll
    (counter==p2start && p2start!=0 && p2start!=p1width) |=> (pulse_on==1'b1)
  );
  ap_syncdown_drive: assert property (cb_pll
    (counter==sync_down && sync_down!=0 && sync_down!=p1width && sync_down!=p2start) |=> (pulse_on==cw && sync_on==1'b0)
  );
  ap_blockoff_drive: assert property (cb_pll
    (counter==block_off && block_off!=0) |=> (inhib==1'b0)
  );

  // -----------------------------
  // Level-hold checks across ranges
  // -----------------------------
  // Pulse shape in CPMG mode (cw==0)
  ap_pulse_hi_pre_p1: assert property (cb_pll
    (cw==1'b0 && counter>0 && counter<p1width) |-> (pulse_on==1'b1)
  );
  ap_pulse_lo_p1_to_p2: assert property (cb_pll
    (cw==1'b0 && counter>p1width && counter<p2start) |-> (pulse_on==1'b0)
  );
  ap_pulse_hi_p2_to_syncdown: assert property (cb_pll
    (cw==1'b0 && counter>p2start && counter<sync_down) |-> (pulse_on==1'b1)
  );
  ap_pulse_lo_post_syncdown: assert property (cb_pll
    (cw==1'b0 && counter>sync_down) |-> (pulse_on==1'b0)
  );

  // Pulse constant in CW mode (cw==1)
  ap_pulse_const_cw: assert property (cb_pll
    (cw==1'b1) |-> (pulse_on==1'b1)
  );

  // Sync level holds
  ap_sync_high_until_down: assert property (cb_pll
    (counter>0 && counter<sync_down) |-> (sync_on==1'b1)
  );
  ap_sync_low_after_down: assert property (cb_pll
    (counter>sync_down) |-> (sync_on==1'b0)
  );

  // Inhibit level holds
  ap_inh_hold_until_off: assert property (cb_pll
    (counter>0 && counter<block_off) |-> (inhib==block)
  );
  ap_inh_low_after_off: assert property (cb_pll
    (counter>block_off) |-> (inhib==1'b0)
  );

  // -----------------------------
  // Coverage
  // -----------------------------
  // CPMG cycle: see all key events in order
  cp_cpmg_cycle: cover property (cb_pll
    (counter==0 && cpmg>0 && p1width>0 && p2width>0 && delay>0)
    ##[1:$] (counter==p1width)
    ##[1:$] (counter==p2start)
    ##[1:$] (counter==sync_down)
    ##[1:$] (counter==block_off)
    ##[1:$] (counter==0)
  );

  // CW cycle: sync_down event and wrap
  cp_cw_cycle: cover property (cb_pll
    (counter==0 && cpmg==0)
    ##[1:$] (counter==sync_down)
    ##[1:$] (counter==0)
  );

  // Inhibit asserted then deasserted within a frame
  cp_inh_toggle: cover property (cb_pll
    (counter==0 && block==1'b1)
    ##[1:$] (counter==block_off && inhib==1'b0)
  );

endmodule

bind pulses pulses_sva();