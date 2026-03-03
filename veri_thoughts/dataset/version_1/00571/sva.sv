// SVA for up_counter
module up_counter_sva #(parameter WIDTH=4)
(
  input logic              clk,
  input logic              rst,   // active-low
  input logic [WIDTH-1:0]  count
);

  default clocking cb @(posedge clk); endclocking

  // Sanity: no X/Z on outputs
  a_no_x_count: assert property (!$isunknown(count));

  // While reset is asserted, count must be zero
  a_hold_zero_in_reset: assert property (!rst |-> count == '0);

  // After reset deasserts, first counted value is 1
  a_first_after_deassert: assert property ($rose(rst) |=> count == 'd1);

  // Increment by 1 every cycle when out of reset (handles wrap-around by width)
  a_inc_when_running: assert property (rst && $past(rst) |-> count == $past(count) + 'd1);

  // Explicit wrap check from all-ones to zero
  a_wrap_to_zero: assert property (rst && $past(rst) && ($past(count) == {WIDTH{1'b1}}) |-> count == '0);

  // Coverage: see reset assert/deassert activity
  c_reset_cycle: cover property ($fell(rst) ##[1:$] $rose(rst));

  // Coverage: observe wrap-around
  c_wrap: cover property (rst && $past(rst) && ($past(count)=={WIDTH{1'b1}}) && (count=='0));

  // Coverage: hit every count value while running
  genvar i;
  generate
    for (i = 0; i < (1<<WIDTH); i++) begin : CVALS
      c_val: cover property (rst && (count == i[WIDTH-1:0]));
    end
  endgenerate

endmodule

// Bind to DUT
bind up_counter up_counter_sva #(.WIDTH(4)) up_counter_sva_b (.clk(clk), .rst(rst), .count(count));