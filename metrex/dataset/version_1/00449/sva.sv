// SVA for up_counter_4bit
module up_counter_4bit_sva (
  input logic       clk,
  input logic       rst,
  input logic [3:0] count
);

  default clocking cb @(posedge clk); endclocking

  // Basic sanity (no X/Z at sampling)
  ap_no_x: assert property (!$isunknown(rst) && !$isunknown(count));

  // Asynchronous reset must drive count to 0 immediately
  ap_async_reset_immediate: assert property (@(posedge rst) count == 4'd0);

  // While reset is asserted, count is 0 at every clock
  ap_reset_holds_zero: assert property (rst |-> count == 4'd0);

  // First clock after reset deasserts: 0 -> 1
  ap_first_after_reset: assert property (!rst && $past(rst) |-> count == 4'd1);

  // Normal operation: increment by 1 every clock when not in reset
  ap_increment: assert property (disable iff (rst)
                                 $past(!rst) |-> count == $past(count) + 4'd1);

  // Explicit wrap check: F -> 0 when not in reset
  ap_wrap: assert property (disable iff (rst)
                            $past(!rst) && $past(count) == 4'hF |-> count == 4'h0);

  // Coverage
  cv_reset_event: cover property (@(posedge rst) 1);
  cv_first_after_reset: cover property (!rst && $past(rst) && count == 4'd1);
  cv_wrap: cover property (disable iff (rst) count == 4'hF ##1 count == 4'h0);
  cv_progress: cover property (disable iff (rst)
                               count == 4'h0 ##1 count == 4'h1 ##1 count == 4'h2 ##1 count == 4'h3);

endmodule

bind up_counter_4bit up_counter_4bit_sva sva_i (.*);