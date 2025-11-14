// SVA for sleep_control
module sleep_control_sva;

  // default clock and reset
  default clocking cb @(posedge CLK); endclocking
  default disable iff (!RESETn);

  // Basic complements and combinational ties
  ap_iso_b:         assert property (MBC_ISOLATE_B == ~MBC_ISOLATE);
  ap_reset_b:       assert property (MBC_RESET_B   == ~MBC_RESET);
  ap_sleep_b:       assert property (MBC_SLEEP_B   == ~MBC_SLEEP);
  ap_wake_ored:     assert property (WAKEUP_REQ_ORED == (WAKEUP_REQ0 | WAKEUP_REQ1 | WAKEUP_REQ2));
  ap_sys_active:    assert property (SYSTEM_ACTIVE == (MBC_SLEEP_B | MBC_ISOLATE_B));

  // Registered relationships
  ap_reset_follows_iso: assert property (MBC_RESET == MBC_ISOLATE);

  // Next-state equations sampled on clock
  ap_iso_eq:        assert property (MBC_ISOLATE   == (MBC_SLEEP_int | ~tran_to_wake));
  ap_sleep_int_eq:  assert property (MBC_SLEEP_int == (MBC_ISOLATE   & ~tran_to_wake));
  ap_sleep_eq:      assert property (MBC_SLEEP     == (MBC_SLEEP_int & MBUS_DIN & ~WAKEUP_REQ_ORED));

  // Combinational helpers
  ap_tran_r_eq:     assert property (tran_to_wake_r == (RESETn & rst_tran_to_wake));
  ap_set_tran_eq:   assert property (set_tran_to_wake == (RESETn & (WAKEUP_REQ_ORED | (MBC_SLEEP_int & ~MBUS_DIN))));
  ap_rst_tran_eq:   assert property (rst_tran_to_wake == ((~RESETn) | (WAKEUP_REQ_ORED | (MBC_SLEEP_int & ~MBUS_DIN) | ~SLEEP_REQ)));

  // Invariants
  ap_sleep_int_implies: assert property (MBC_SLEEP_int |-> (MBC_ISOLATE && !tran_to_wake));
  ap_deiso_implies:     assert property (!MBC_ISOLATE |-> (!MBC_SLEEP_int && tran_to_wake));
  ap_sleep_implies:     assert property (MBC_SLEEP |-> (MBC_SLEEP_int && MBUS_DIN && !WAKEUP_REQ_ORED));

  // Asynchronous behaviors
  // On entering reset, flops go to 1 on the next simulation time slot
  ap_async_reset_vals: assert property (@(negedge RESETn) 1 |=> (MBC_ISOLATE && MBC_RESET && MBC_SLEEP_int));
  // SR latch-like handshakes for tran_to_wake
  ap_tran_set:   assert property (@(posedge set_tran_to_wake) 1 |=> tran_to_wake);
  ap_tran_reset: assert property (@(negedge tran_to_wake_r)   1 |=> !tran_to_wake);

  // No-X on key outputs
  ap_no_x_outs: assert property (!$isunknown({MBC_ISOLATE,MBC_ISOLATE_B,MBC_RESET,MBC_RESET_B,
                                              MBC_SLEEP,MBC_SLEEP_B,SYSTEM_ACTIVE,WAKEUP_REQ_ORED})));

  // Liveness: wake request de-isolates quickly
  ap_wake_deiso: assert property (WAKEUP_REQ_ORED |-> ##[0:2] (!MBC_ISOLATE && !MBC_RESET));

  // Coverage
  cv_reset_entry:       cover property (@(negedge RESETn) 1 |=> (MBC_ISOLATE && MBC_RESET));
  cv_deiso:             cover property ($rose(WAKEUP_REQ_ORED) ##[0:2] (!MBC_ISOLATE));
  cv_sleep_entry:       cover property ((SLEEP_REQ && MBUS_DIN && !WAKEUP_REQ_ORED) ##[1:3] MBC_SLEEP);
  cv_iso_toggles:       cover property ($changed(MBC_ISOLATE));
  cv_sleep_toggles:     cover property ($changed(MBC_SLEEP));
  cv_tran_set_reset:    cover property ($rose(set_tran_to_wake) ##[0:2] tran_to_wake ##[0:2] $fell(rst_tran_to_wake) ##[0:1] !tran_to_wake);
  cv_wake0:             cover property ($rose(WAKEUP_REQ0) ##[0:2] (!MBC_ISOLATE));
  cv_wake1:             cover property ($rose(WAKEUP_REQ1) ##[0:2] (!MBC_ISOLATE));
  cv_wake2:             cover property ($rose(WAKEUP_REQ2) ##[0:2] (!MBC_ISOLATE));

endmodule

bind sleep_control sleep_control_sva sva_i();