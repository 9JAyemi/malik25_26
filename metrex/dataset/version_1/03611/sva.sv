// SVA for PWM. Bind this to the DUT to check behavior and get coverage.

module PWM_sva #(
  parameter int unsigned clk_freq = 50_000_000,
  parameter int unsigned pwm_freq = 1_000
) (
  input  logic         clk,
  input  logic  [7:0]  in,
  input  logic         out,
  input  logic [31:0]  counter,
  input  logic  [7:0]  threshold
);
  localparam int unsigned PER = clk_freq / pwm_freq;

  // init gating for first-cycle $past usage
  bit init;
  always_ff @(posedge clk) init <= 1'b1;

  default clocking cb @(posedge clk); endclocking
  default disable iff (!init);

  // Counter range and progression
  a_cnt_range:        assert property (counter inside {[0:PER]});
  a_cnt_inc:          assert property ($past(counter) <  PER |-> counter == $past(counter) + 1);
  a_cnt_wrap_p2n:     assert property ($past(counter) == PER |-> counter == 0);
  a_cnt_wrap_n2p:     assert property (counter == 0 |-> $past(counter) == PER);
  a_cnt_zero_spacing: assert property ((counter == 0) |-> (counter != 0)[*PER] ##1 (counter == 0));

  // Threshold latching behavior
  a_thr_updates_only_at_wrap: assert property ($changed(threshold) |-> (counter == 0 && $past(counter) == PER));
  a_thr_sampled_from_in:      assert property (($past(counter) == PER) |-> threshold == $past(in));
  a_thr_stable_within_period: assert property (counter != 0 |-> $stable(threshold));

  // Output function and edge alignment
  a_out_def:   assert property (out == (counter < threshold));
  a_out_rise:  assert property ($rose(out) |-> (counter == 0 && threshold > 0));
  a_out_fall:  assert property ($fell(out) |-> (counter == threshold));

  // Basic coverage
  c_wrap:       cover property (counter == PER ##1 counter == 0);
  c_thr_0:      cover property (counter == 0 && threshold == 8'h00);
  c_thr_1:      cover property (counter == 0 && threshold == 8'h01);
  c_thr_mid:    cover property (counter == 0 && threshold == 8'h80);
  c_thr_max:    cover property (counter == 0 && threshold == 8'hFF);
  c_out_rise:   cover property ($rose(out));
  c_out_fall:   cover property ($fell(out));
  c_0pct:       cover property (counter == 0 && threshold == 0 ##1 (out == 0)[*PER+1]);
  c_100pct:     cover property (counter == 0 && threshold > PER ##1 (out == 1)[*PER+1]);

endmodule

// Bind to DUT (accesses internal counter/threshold)
bind PWM PWM_sva #(.clk_freq(clk_freq), .pwm_freq(pwm_freq)) pwm_sva_i (
  .clk(clk),
  .in(in),
  .out(out),
  .counter(counter),
  .threshold(threshold)
);