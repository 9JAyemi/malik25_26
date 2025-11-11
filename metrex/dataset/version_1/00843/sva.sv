// SVA for up_down_counter
module up_down_counter_sva (
  input logic        clk,
  input logic        reset,     // active-high, synchronous
  input logic        up_down,   // 1=up, 0=down
  input logic [3:0]  q
);
  default clocking cb @(posedge clk); endclocking

  // Sanity: no X/Z on critical signals
  ap_inputs_known: assert property (!$isunknown({reset, up_down}));
  ap_q_known     : assert property (!$isunknown(q));

  // Reset behavior: next cycle must be 0 while reset is asserted
  ap_reset_next0 : assert property (reset |=> (q == 4'd0));

  // Next-state function (mod-16 arithmetic)
  ap_inc:  assert property (!reset && up_down   |=> q == ($past(q) + 4'd1));
  ap_dec:  assert property (!reset && !up_down  |=> q == ($past(q) - 4'd1));

  // Explicit wrap-around checks
  ap_wrap_up  : assert property (!reset && up_down   && ($past(q) == 4'hF) |=> (q == 4'h0));
  ap_wrap_down: assert property (!reset && !up_down  && ($past(q) == 4'h0) |=> (q == 4'hF));

  // Coverage: reset, both directions, and both wraps
  cp_reset      : cover property (reset);
  cp_inc        : cover property (!reset && up_down);
  cp_dec        : cover property (!reset && !up_down);
  cp_wrap_up    : cover property (!reset && up_down   && ($past(q) == 4'hF) |=> (q == 4'h0));
  cp_wrap_down  : cover property (!reset && !up_down  && ($past(q) == 4'h0) |=> (q == 4'hF));
  // Mixed direction activity
  cp_mix        : cover property (!reset && up_down ##1 !reset && !up_down);
endmodule

// Bind into the DUT
bind up_down_counter up_down_counter_sva u_up_down_counter_sva (
  .clk(clk), .reset(reset), .up_down(up_down), .q(q)
);