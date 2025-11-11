// SVA for up_down_counter
module up_down_counter_sva (
  input clk,
  input reset,
  input enable,
  input direction,
  input [3:0] count
);

  default clocking cb @(posedge clk); endclocking

  // Basic correctness
  assert property (reset |=> count == 4'd0);

  assert property (disable iff (reset)
                   !enable |=> $stable(count));

  assert property (disable iff (reset)
                   enable && direction && count != 4'd15 |=> count == $past(count) + 4'd1);

  assert property (disable iff (reset)
                   enable && direction && count == 4'd15 |=> count == 4'd0);

  assert property (disable iff (reset)
                   enable && !direction && count != 4'd0 |=> count == $past(count) - 4'd1);

  assert property (disable iff (reset)
                   enable && !direction && count == 4'd0 |=> count == 4'd15);

  // Count changes only due to enable or reset action
  assert property ((count != $past(count)) |-> ($past(enable) || $past(reset)));

  // No X/Z on critical signals (post-reset for count)
  assert property (!$isunknown({enable, direction}));
  assert property (disable iff (reset) !$isunknown(count));

  // Coverage
  cover property (reset |=> count == 4'd0);
  cover property (disable iff (reset)
                  enable && direction && count != 4'd15 |=> count == $past(count) + 4'd1);
  cover property (disable iff (reset)
                  enable && direction && count == 4'd15 |=> count == 4'd0);
  cover property (disable iff (reset)
                  enable && !direction && count != 4'd0 |=> count == $past(count) - 4'd1);
  cover property (disable iff (reset)
                  enable && !direction && count == 4'd0 |=> count == 4'd15);
  cover property (disable iff (reset)
                  !enable |=> $stable(count));

endmodule

bind up_down_counter up_down_counter_sva u_up_down_counter_sva (.*);