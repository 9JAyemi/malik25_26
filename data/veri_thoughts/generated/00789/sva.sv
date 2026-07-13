module counter_2bit_async_reset_sync_enable_sva (
  input logic CLK,
  input logic EN,
  input logic RST,
  input logic [1:0] Q
);

  ///// Reset behavior /////
  // Reset high causes Q to be 0 on the following clock.
  check_reset_clears_next: assert property (
    @(posedge CLK) RST |=> (Q == 2'b00)
  );

  // If reset was high on the previous clock, Q must be 0 now.
  check_prev_reset_forces_zero: assert property (
    @(posedge CLK) $past(RST) |-> (Q == 2'b00)
  );

  // Immediately after reset deasserts, Q is still 0 before any enable update.
  check_deassert_reset_prestate_zero: assert property (
    @(posedge CLK) $past(RST) && !RST |-> (Q == 2'b00)
  );

  // While reset stays asserted across consecutive clocks, Q is 0 now.
  check_hold_zero_during_continuous_reset_now: assert property (
    @(posedge CLK) ($past(RST) && RST) |-> (Q == 2'b00)
  );

  // While reset stays asserted across consecutive clocks, Q is 0 on the next clock.
  check_hold_zero_during_continuous_reset_next: assert property (
    @(posedge CLK) ($past(RST) && RST) |=> (Q == 2'b00)
  );

  ///// Enable and wrap behavior (robust to async reset) /////
  // With EN high and Q at 3, the next value wraps to 0 (reset may also force 0).
  check_wrap_on_en_from_3: assert property (
    @(posedge CLK) disable iff (RST) (EN && (Q == 2'b11)) |=> (Q == 2'b00)
  );

  // If Q was 0 and EN was low last cycle (not in reset), Q remains 0 now.
  check_zero_stays_zero_without_enable: assert property (
    @(posedge CLK) disable iff (RST) ($past(EN) == 1'b0 && $past(Q) == 2'b00) |-> (Q == 2'b00)
  );

endmodule