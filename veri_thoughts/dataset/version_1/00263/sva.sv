// SVA for soft_clock — concise, high-quality checks and coverage
// Bind this module to the DUT instance (see bind at bottom).

module soft_clock_sva #(
  parameter C_SIPIF_DWIDTH = 32
)(
  input  logic                                Bus2IP_Reset,
  input  logic                                Bus2IP_Clk,
  input  logic                                Bus2IP_WrCE,
  input  logic [0:C_SIPIF_DWIDTH-1]           Bus2IP_Data,
  input  logic [0:(C_SIPIF_DWIDTH/8)-1]       Bus2IP_BE,

  input  logic                                Clk2IP_Clk,
  input  logic                                Clk2Bus_WrAck,
  input  logic                                Clk2Bus_Error,
  input  logic                                Clk2Bus_ToutSup,

  // Internal state taps
  input  logic                                isr_ce,
  input  logic                                isr_error
);

  // Golden decode (matches DUT intent and bit ordering)
  localparam logic [0:3] CLOCK_ENABLE  = 4'b1010;
  localparam logic [0:3] CLOCK_DISABLE = 4'b0101;

  wire logic [0:3] top_nibble = Bus2IP_Data[C_SIPIF_DWIDTH-4 : C_SIPIF_DWIDTH-1];
  wire logic       top_be     = Bus2IP_BE[(C_SIPIF_DWIDTH/8)-1];

  wire logic en_match  = (top_nibble == CLOCK_ENABLE);
  wire logic dis_match = (top_nibble == CLOCK_DISABLE);
  wire logic match     = en_match | dis_match;
  wire logic mismatch  = ~match;

  default clocking cb @(posedge Bus2IP_Clk); endclocking

  // Reset behavior
  a_reset_vals:       assert property (cb Bus2IP_Reset |-> (isr_ce==1'b1 && isr_error==1'b0 && Clk2Bus_ToutSup==1'b1));
  a_toutsup_eq_reset: assert property (cb Clk2Bus_ToutSup == Bus2IP_Reset);

  // Clock gating correctness (sampled on both edges)
  a_clk_gate_pos: assert property (@(posedge Bus2IP_Clk) Clk2IP_Clk == isr_ce);
  a_clk_gate_neg: assert property (@(negedge Bus2IP_Clk) Clk2IP_Clk == 1'b0);

  // isr_ce update rules
  a_ce_enable:           assert property (cb disable iff (Bus2IP_Reset) (Bus2IP_WrCE && top_be && en_match)  |=> isr_ce==1'b1);
  a_ce_disable:          assert property (cb disable iff (Bus2IP_Reset) (Bus2IP_WrCE && top_be && dis_match) |=> isr_ce==1'b0);
  a_ce_hold_mismatch:    assert property (cb disable iff (Bus2IP_Reset) (Bus2IP_WrCE && top_be && mismatch)  |=> isr_ce==$past(isr_ce));
  a_ce_hold_be0:         assert property (cb disable iff (Bus2IP_Reset) (Bus2IP_WrCE && !top_be)             |=> isr_ce==$past(isr_ce));
  a_ce_stable_no_write:  assert property (cb disable iff (Bus2IP_Reset) (!Bus2IP_WrCE)                       |=> isr_ce==$past(isr_ce));

  // isr_error update/hold rules (note: BE does not gate isr_error in DUT)
  a_err_update_on_wr: assert property (cb disable iff (Bus2IP_Reset) Bus2IP_WrCE |=> (isr_error == mismatch));
  a_err_hold_no_wr:   assert property (cb disable iff (Bus2IP_Reset) !Bus2IP_WrCE |=> (isr_error == $past(isr_error)));

  // Output response definitions and mutual exclusion
  a_ack_def:        assert property (cb Clk2Bus_WrAck == (match    && Bus2IP_WrCE && top_be));
  a_err_def:        assert property (cb Clk2Bus_Error == (mismatch && Bus2IP_WrCE && top_be));
  a_ack_err_mutex:  assert property (cb !(Clk2Bus_WrAck && Clk2Bus_Error));
  a_no_resp_wo_wr:  assert property (cb (!Bus2IP_WrCE || !top_be) |-> (!Clk2Bus_WrAck && !Clk2Bus_Error));

  // Decode sanity
  a_exclusive_matches: assert property (cb !(en_match && dis_match));
  a_match_partition:   assert property (cb match == !mismatch);

  // Coverage: key behaviors
  c_enable_wr:         cover property (cb disable iff (Bus2IP_Reset) Bus2IP_WrCE && top_be && en_match  && Clk2Bus_WrAck);
  c_disable_wr:        cover property (cb disable iff (Bus2IP_Reset) Bus2IP_WrCE && top_be && dis_match && Clk2Bus_WrAck);
  c_mismatch_error:    cover property (cb disable iff (Bus2IP_Reset) Bus2IP_WrCE && top_be && mismatch  && Clk2Bus_Error);
  c_be0_suppressed:    cover property (cb disable iff (Bus2IP_Reset) (Bus2IP_WrCE && !top_be && match) |=> (!Clk2Bus_WrAck && !Clk2Bus_Error && isr_ce==$past(isr_ce)));
  c_ce_toggle_down:    cover property (cb disable iff (Bus2IP_Reset) (isr_ce==1'b1) ##1 (Bus2IP_WrCE && top_be && dis_match) ##1 (isr_ce==1'b0));
  c_ce_toggle_up:      cover property (cb disable iff (Bus2IP_Reset) (isr_ce==1'b0) ##1 (Bus2IP_WrCE && top_be && en_match)  ##1 (isr_ce==1'b1));
  c_err_latch_clear:   cover property (cb disable iff (Bus2IP_Reset) (Bus2IP_WrCE && mismatch) ##1 (!Bus2IP_WrCE && isr_error) ##1 (Bus2IP_WrCE && match) ##1 (isr_error==1'b0));

endmodule

// Bind to all instances of soft_clock
bind soft_clock soft_clock_sva #(.C_SIPIF_DWIDTH(C_SIPIF_DWIDTH)) soft_clock_sva_i (
  .Bus2IP_Reset     (Bus2IP_Reset),
  .Bus2IP_Clk       (Bus2IP_Clk),
  .Bus2IP_WrCE      (Bus2IP_WrCE),
  .Bus2IP_Data      (Bus2IP_Data),
  .Bus2IP_BE        (Bus2IP_BE),
  .Clk2IP_Clk       (Clk2IP_Clk),
  .Clk2Bus_WrAck    (Clk2Bus_WrAck),
  .Clk2Bus_Error    (Clk2Bus_Error),
  .Clk2Bus_ToutSup  (Clk2Bus_ToutSup),
  .isr_ce           (isr_ce),
  .isr_error        (isr_error)
);