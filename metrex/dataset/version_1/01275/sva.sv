// SVA for signal_module
// Focus: correctness of update/hold, overflow detection, parity behavior, reset, and X-propagation

module signal_module_sva (
  input logic        clk,
  input logic        reset,
  input logic [3:0]  data_in,
  input logic        enable,
  input logic [3:0]  data_out,
  input logic        parity,
  input logic        overflow,
  input logic        underflow
);

  // Establish a valid $past() window
  bit past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  // 5-bit sum using previous data_out and current data_in
  let SUM5 = {1'b0, $past(data_out)} + {1'b0, data_in};

  // Reset clears all outputs (synchronous reset)
  ap_reset_clear: assert property (@(posedge clk)
    reset |=> (data_out == 4'h0 && parity == 1'b0 && overflow == 1'b0 && underflow == 1'b0)
  );

  // Hold behavior when disabled
  ap_hold_when_disabled: assert property (@(posedge clk) disable iff (reset)
    past_valid && !enable |-> (data_out == $past(data_out) &&
                               parity   == $past(parity)   &&
                               overflow == $past(overflow) &&
                               underflow== $past(underflow))
  );

  // Update behavior when enabled: modulo-16 sum, parity toggle, correct overflow, no underflow
  ap_update_when_enabled: assert property (@(posedge clk) disable iff (reset)
    past_valid && enable |-> (data_out == SUM5[3:0] &&
                              parity   == ~ $past(parity) &&
                              overflow == SUM5[4] &&
                              underflow== 1'b0)
  );

  // Underflow should never assert (unsigned add cannot be < 0)
  ap_never_underflow: assert property (@(posedge clk) disable iff (reset)
    !underflow
  );

  // No X/Z on observable outputs after reset releases
  ap_no_x: assert property (@(posedge clk) disable iff (reset)
    past_valid |-> !$isunknown({data_out, parity, overflow, underflow})
  );

  // Coverage
  cp_reset_seen:            cover property (@(posedge clk) reset);
  cp_update_no_overflow:    cover property (@(posedge clk) disable iff (reset)
                              past_valid && enable && !SUM5[4]);
  cp_update_overflow:       cover property (@(posedge clk) disable iff (reset)
                              past_valid && enable &&  SUM5[4]);
  cp_parity_toggles:        cover property (@(posedge clk) disable iff (reset)
                              past_valid && enable && (parity == ~ $past(parity)));

endmodule

bind signal_module signal_module_sva sva_inst (.*);