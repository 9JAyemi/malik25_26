module up_down_counter_sva (
  input logic clk,
  input logic reset,       // active-low asynchronous reset in RTL
  input logic enable,
  input logic mode,        // 0: up, 1: down
  input logic [2:0] q
);

  ///// Reset behavior /////
  // While reset is asserted low, q is forced to 0.
  reset_forces_zero: assert property (
    @(posedge clk) (!reset) |-> (q == 3'b000)
  );

  ///// Enable gating /////
  // When enable is LOW, q holds its previous value.
  hold_when_disabled: assert property (
    @(posedge clk) disable iff (!reset) (!enable) |=> (q == $past(q))
  );

  // q only changes when enable was HIGH in the previous cycle (excluding reset effects).
  change_only_when_enabled: assert property (
    @(posedge clk) disable iff (!reset) (q != $past(q)) |-> $past(enable)
  );

  ///// Up mode behavior (mode == 0) /////
  // In up mode with enable, non-wrap increment by 1.
  upmode_inc_nonwrap: assert property (
    @(posedge clk) disable iff (!reset) (enable && !mode && (q != 3'b111)) |=> (q == $past(q) + 3'b001)
  );

  // In up mode with enable, wrap from 7 to 0.
  upmode_wrap_from_max: assert property (
    @(posedge clk) disable iff (!reset) (enable && !mode && (q == 3'b111)) |=> (q == 3'b000)
  );

  // In up mode with enable, wrap occurs iff previous q was 7.
  upmode_wrap_iff_prev_max: assert property (
    @(posedge clk) disable iff (!reset) (enable && !mode) |=> (($past(q) == 3'b111) == (q == 3'b000))
  );

  ///// Down mode behavior (mode == 1) /////
  // In down mode with enable, non-wrap decrement by 1.
  downmode_dec_nonwrap: assert property (
    @(posedge clk) disable iff (!reset) (enable && mode && (q != 3'b000)) |=> (q == $past(q) - 3'b001)
  );

  // In down mode with enable, wrap from 0 to 7.
  downmode_wrap_from_zero: assert property (
    @(posedge clk) disable iff (!reset) (enable && mode && (q == 3'b000)) |=> (q == 3'b111)
  );

  // In down mode with enable, wrap occurs iff previous q was 0.
  downmode_wrap_iff_prev_zero: assert property (
    @(posedge clk) disable iff (!reset) (enable && mode) |=> (($past(q) == 3'b000) == (q == 3'b111))
  );

  ///// General enabled behavior /////
  // When enabled, q must change every cycle (either +/-1 with wrap).
  enabled_always_changes: assert property (
    @(posedge clk) disable iff (!reset) enable |=> (q != $past(q))
  );

endmodule