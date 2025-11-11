// SVA checker for counter_4bit_async
module counter_4bit_async_sva (
  input clk,
  input rst,        // active-low async reset
  input en,
  input [3:0] out
);

  // 1) Out must be 0 whenever reset is low (sampled on clk)
  property p_reset_low_out_zero;
    @(posedge clk) (!rst) |-> (out == 4'h0);
  endproperty
  assert property (p_reset_low_out_zero);

  // 2) After an async reset fall between clocks, out must be 0 on the next clk edge
  property p_async_clear_before_next_clk;
    @(posedge clk) $fell(rst) |-> (out == 4'h0);
  endproperty
  assert property (p_async_clear_before_next_clk);

  // 3) When enabled, increment by 1 modulo 16 on each clk
  property p_inc_when_en;
    @(posedge clk) disable iff (!rst)
      en |=> (out == $past(out) + 4'd1);
  endproperty
  assert property (p_inc_when_en);

  // 4) When disabled, hold value
  property p_hold_when_dis;
    @(posedge clk) disable iff (!rst)
      !en |=> (out == $past(out));
  endproperty
  assert property (p_hold_when_dis);

  // 5) Any change to out (while not in reset) must be due to en
  property p_change_requires_en;
    @(posedge clk) disable iff (!rst)
      (out != $past(out)) |-> $past(en);
  endproperty
  assert property (p_change_requires_en);

  // 6) Explicit wrap-around check (F -> 0) when enabled
  property p_wrap;
    @(posedge clk) disable iff (!rst)
      ($past(out) == 4'hF && en) |=> (out == 4'h0);
  endproperty
  assert property (p_wrap);

  // 7) No X/Z on key signals
  property p_no_x_on_clk_sample;
    @(posedge clk) !$isunknown({rst, en, out});
  endproperty
  assert property (p_no_x_on_clk_sample);

  // Coverage

  // a) See an async reset event
  cover property (@(negedge rst) 1);

  // b) See at least one increment
  cover property (@(posedge clk) disable iff (!rst)
                  en ##1 (out == $past(out) + 4'd1));

  // c) See hold when disabled across two cycles
  cover property (@(posedge clk) disable iff (!rst)
                  !en [*2] and (out == $past(out,1)));

  // d) See wrap from F to 0 with enable
  cover property (@(posedge clk) disable iff (!rst)
                  (out == 4'hF && en) ##1 (out == 4'h0));

endmodule

// Bind to DUT
bind counter_4bit_async counter_4bit_async_sva u_counter_4bit_async_sva (.*);