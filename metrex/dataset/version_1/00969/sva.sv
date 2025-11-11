// SVA for counter_2bit
module counter_2bit_sva (
  input  logic       clk,
  input  logic       rst,   // active-low async reset
  input  logic [1:0] count
);

  default clocking cb @(posedge clk); endclocking

  // Async reset clears immediately
  a_async_clear: assert property (@(negedge rst) count == 2'b00);

  // Hold 0 while in reset
  a_hold_in_reset: assert property (!rst |-> (count == 2'b00) throughout (!rst));

  // First cycle after reset release must start at 1 (because async set to 0 then +1)
  a_first_after_release: assert property ($rose(rst) |-> count == 2'b01);

  // Normal increment when reset has been high for consecutive cycles
  a_inc_when_running: assert property (disable iff (!rst)
                                       $past(rst) |-> count == $past(count) + 2'b01);

  // No X/Z on count at any clock (and at reset assertion edge)
  a_no_x_clk:  assert property (@(posedge clk) !$isunknown(count));
  a_no_x_rst:  assert property (@(negedge rst) !$isunknown(count));

  // Coverage: observe full cycle after reset release and a wrap 3->0
  c_full_cycle_after_release: cover property ($rose(rst)
                                             ##1 (count==2'b01)
                                             ##1 (count==2'b10)
                                             ##1 (count==2'b11)
                                             ##1 (count==2'b00));
  c_wrap: cover property (disable iff(!rst) (count==2'b11) ##1 (count==2'b00));
  c_reset_assert: cover property (@(negedge rst) 1'b1);

endmodule

// Bind into DUT
bind counter_2bit counter_2bit_sva u_counter_2bit_sva (.clk(clk), .rst(rst), .count(count));