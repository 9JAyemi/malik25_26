// SVA for counter: modulo-1000 up-counter with wrap at 999
module counter_sva (
  input logic        clk,
  input logic [9:0]  count
);
  default clocking cb @(posedge clk); endclocking

  // Next-state check (X-safe): +1, wrap at 999 -> 0
  property p_step_mod1000;
    !$isunknown($past(count)) |->
      count == (($past(count) == 10'd999) ? 10'd0 : $past(count) + 10'd1);
  endproperty
  assert property (p_step_mod1000);

  // Once in-range, always in-range (X-safe)
  property p_range_invariant;
    ($past(count inside {[10'd0:10'd999]}) && !$isunknown($past(count))) |->
      (count inside {[10'd0:10'd999]});
  endproperty
  assert property (p_range_invariant);

  // Periodicity: value repeats every 1000 cycles (when history known)
  property p_period_1000;
    !$isunknown($past(count,1000)) |-> (count == $past(count,1000));
  endproperty
  assert property (p_period_1000);

  // Coverage: observe wrap and a full cycle
  cover property (count == 10'd999 ##1 count == 10'd0);
  cover property (count == 10'd0   ##1000 count == 10'd0);
endmodule

// Bind into DUT
bind counter counter_sva u_counter_sva (.clk(clk), .count(count));