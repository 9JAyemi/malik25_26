// SVA for decade_counter and top_module.
// Bind these modules into the DUT for assertion-based verification.

module decade_counter_sva (
    input clk,
    input slowena,
    input reset,
    input pause,
    input [3:0] q,
    input [3:0] johnson_q,
    input       pause_count
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Reset drives regs to zero on the cycle after reset is seen.
  assert property ($rose(reset) |=> (johnson_q==4'b0000 && q==4'b0000 && pause_count==1'b0));

  // Johnson counter state update semantics
  // - advance when enabled, hold when not enabled
  assert property ($past(!reset) |-> (johnson_q ==
                       ($past(slowena)
                          ? { $past(johnson_q[2:0]), ~|$past(johnson_q) }
                          :  $past(johnson_q))));

  // Johnson counter encoding safety: only 0000 or one-hot
  assert property ((johnson_q==4'b0000) || $onehot(johnson_q));

  // q updates only when not paused and not in holdoff
  assert property ($past(!reset) && (!pause && (pause_count==1'b0)) |=> (q == $past(johnson_q)));

  // q holds value while paused or in holdoff window
  assert property ($past(!reset) && (pause || (pause_count==1'b1)) |=> (q == $past(q)));

  // pause_count behavior (1-bit register)
  assert property ($past(!reset) && pause |=> (pause_count==1'b1));
  assert property ($past(!reset) && !pause && ($past(pause_count)==1'b1) |=> (pause_count == ($past(pause_count)+1'b1))); // wraps to 0
  assert property ($past(!reset) && !pause && ($past(pause_count)==1'b0) |=> (pause_count==1'b0));

  // Coverage
  cover property (!pause && (pause_count==1'b0) ##1 (q==$past(johnson_q)));
  cover property (johnson_q==4'b1000 ##1 johnson_q==4'b0000); // wrap-around
  cover property (pause); // see if pause ever triggers
endmodule

bind decade_counter decade_counter_sva dc_sva_bind (.*);

module top_module_sva (
    input clk,
    input slowena,
    input reset,
    input [3:0] q,
    input       pause,
    input       slow_clk
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Reset initializes slow_clk low on next cycle
  assert property ($rose(reset) |=> slow_clk==1'b0);

  // slow_clk toggles iff slowena is high; holds otherwise
  assert property ($past(!reset) |-> (slow_clk == ($past(slowena) ? ~$past(slow_clk) : $past(slow_clk))));

  // pause is exactly q==4'b1001
  assert property (pause == (q==4'b1001));

  // Coverage: see slow clock toggling and any pause
  cover property ($past(slowena) && (slow_clk != $past(slow_clk)));
  cover property (pause);
endmodule

bind top_module top_module_sva top_sva_bind (.*);