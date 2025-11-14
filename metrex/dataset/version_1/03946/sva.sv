// SVA for majority_counter and submodules. Bind these to the DUT.

module mc_sva;
  // Bound into majority_counter scope
  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Final output must hold when disabled
  a_hold_when_disabled: assert property (!enable |-> final_output == $past(final_output));

  // Selection: when enable and LSB of counter was 1, latch counter (zero-extended)
  a_sel_counter: assert property (
    $past(enable) && $past(counter_out[0]) |-> (final_output[7:4] == 4'b0000 && final_output[3:0] == $past(counter_out))
  );

  // Selection: when enable and LSB of counter was 0, latch majority Y (zero-extended)
  a_sel_Y: assert property (
    $past(enable) && !$past(counter_out[0]) |-> (final_output == {7'b0, $past(Y)})
  );

  // Majority gate functional check (sampled on clk)
  a_majority: assert property (
    Y == ((A & B & C) | (A & B & D) | (A & C & D) | (B & C & D))
  );

  // counter_out_even definition check
  a_even_def: assert property (
    counter_out_even == (counter_out[0] ? counter_out[1:0] : counter_out[2:1])
  );

  // Known-value checks (post-reset)
  a_no_x_outputs: assert property (!$isunknown({final_output, Y, counter_out, counter_out_even}));

  // Asynchronous reset on final_output
  a_rst_async_final: assert property (@(posedge reset) final_output == 8'h00);
  // While reset is asserted, final_output must be 0 at each clk
  a_rst_sync_final:  assert property (@(posedge clk) reset |-> final_output == 8'h00);

  // Coverage
  c_take_counter: cover property ($past(enable) && $past(counter_out[0]) &&
                                  final_output[3:0] == $past(counter_out));
  c_take_y0:      cover property ($past(enable) && !$past(counter_out[0]) &&
                                  $past(Y) == 1'b0 && final_output == 8'h00);
  c_take_y1:      cover property ($past(enable) && !$past(counter_out[0]) &&
                                  $past(Y) == 1'b1 && final_output == 8'h01);
  c_even_sel0:    cover property (counter_out[0] == 1'b0);
  c_even_sel1:    cover property (counter_out[0] == 1'b1);
endmodule

bind majority_counter mc_sva mc_sva_i();


module counter_sva;
  // Bound into counter scope
  default clocking cb @(posedge clk); endclocking

  // Async reset behavior
  a_cnt_async_reset: assert property (@(posedge reset) out == 4'h0);
  // While reset asserted, out must be 0 at each clk
  a_cnt_hold_reset:  assert property (reset |-> out == 4'h0);

  // Increment when enabled, hold when disabled (mod-16)
  a_cnt_inc:  assert property (disable iff (reset) enable  |-> out == $past(out) + 4'h1);
  a_cnt_hold: assert property (disable iff (reset) !enable |-> out == $past(out));

  // Known-value check
  a_cnt_no_x: assert property (disable iff (reset) !$isunknown(out));

  // Coverage
  c_cnt_inc:  cover property (disable iff (reset) enable && out == $past(out) + 4'h1);
  c_cnt_wrap: cover property (disable iff (reset) $past(out) == 4'hF && enable && out == 4'h0);
endmodule

bind counter counter_sva counter_sva_i();