// SVA for watchdog_timer
module watchdog_timer_sva (
  input logic         clk,
  input logic         reset,
  input logic [31:0]  timeout,
  input logic [31:0]  counter,
  input logic         wd_reset
);

  logic past_valid;
  initial past_valid = 1'b0;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // Reset drives known zeros
  assert property (@(posedge clk) reset |-> (counter==32'd0 && wd_reset==1'b0));
  // Held reset keeps zeros
  assert property (@(posedge clk) past_valid && reset && $past(reset) |-> (counter==32'd0 && wd_reset==1'b0));

  // Counter increments by 1 every cycle out of reset (mod 2^32)
  assert property (@(posedge clk) (!reset && past_valid) |-> counter == $past(counter)+32'd1);

  // wd_reset is a 1-cycle pulse exactly when previous counter equals timeout
  assert property (@(posedge clk) (!reset && past_valid) |-> (wd_reset == ($past(counter)==timeout)));
  assert property (@(posedge clk) disable iff (reset) wd_reset |-> ##1 !wd_reset);

  // First cycle after reset deassertion: counter=1, wd_reset reflects timeout==0
  assert property (@(posedge clk) past_valid && $past(reset) && !reset |-> (counter==32'd1 && wd_reset==(timeout==32'd0)));

  // No Xs in key signals out of reset
  assert property (@(posedge clk) disable iff (reset) !$isunknown({wd_reset,counter,timeout}));

  // Coverage
  // See at least one wd_reset after reset release (any timeout)
  cover property (@(posedge clk) past_valid && $past(reset) && !reset ##[0:$] wd_reset);
  // See two wd_reset pulses (wrap-around scenario)
  cover property (@(posedge clk) disable iff (reset) wd_reset ##[1:$] wd_reset);
  // Corner: timeout==0 causes immediate pulse after reset release
  cover property (@(posedge clk) past_valid && $past(reset) && !reset && (timeout==32'd0) && wd_reset);

endmodule

// Bind example:
// bind watchdog_timer watchdog_timer_sva sva(.clk(clk), .reset(reset), .timeout(timeout), .counter(counter), .wd_reset(wd_reset));