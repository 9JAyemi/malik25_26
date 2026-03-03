// SVA for binary_counter
// Concise, high-quality checks + useful coverage

module binary_counter_sva #(parameter WIDTH=4) (
  input logic                 clk,
  input logic                 reset,
  input logic                 enable,
  input logic [WIDTH-1:0]     q
);

  // Asynchronous reset drives q to 0 immediately (post-NBA in same timestep)
  ap_async_reset_zero: assert property (@(posedge reset) ##0 (q == '0));

  // When reset is high at a clock edge, q must be 0 (post-NBA at that edge)
  ap_sync_observe_reset_zero: assert property (@(posedge clk) reset |-> ##0 (q == '0));

  // q must never be X/Z at clock edges and after reset assertion
  ap_q_known_clk:   assert property (@(posedge clk)  !$isunknown(q));
  ap_q_known_reset: assert property (@(posedge reset) ##0 !$isunknown(q));

  // Functional behavior on clock edges when not in reset
  // Hold when disabled
  ap_hold_when_disabled: assert property (@(posedge clk) disable iff (reset)
                                          !enable |=> q == $past(q));
  // Increment by 1 (mod 2^WIDTH) when enabled
  ap_inc_when_enabled:   assert property (@(posedge clk) disable iff (reset)
                                          enable |=> q == ($past(q) + WIDTH'(1)));

  // Minimal coverage
  // See a reset event
  cp_reset:     cover property (@(posedge reset) 1);
  // See a hold cycle
  cp_hold:      cover property (@(posedge clk) disable iff (reset)
                                !enable |=> q == $past(q));
  // See an increment
  cp_inc:       cover property (@(posedge clk) disable iff (reset)
                                enable |=> q == ($past(q) + WIDTH'(1)));
  // See wrap-around from max to zero
  cp_wrap:      cover property (@(posedge clk) disable iff (reset)
                                $past(q) == {WIDTH{1'b1}} && enable |=> q == '0);
  // See enable toggle around counting
  cp_en_toggle: cover property (@(posedge clk) disable iff (reset)
                                !enable ##1 enable ##1 !enable);

endmodule

// Bind into the DUT
bind binary_counter binary_counter_sva #(.WIDTH(4)) u_binary_counter_sva (
  .clk(clk),
  .reset(reset),
  .enable(enable),
  .q(q)
);