// SVA for up_counter
module up_counter_sva #(parameter WIDTH=4)
(
  input logic                clk,
  input logic                reset_n,
  input logic [WIDTH-1:0]    count
);

  default clocking cb @(posedge clk); endclocking

  // Assertions
  // Async reset immediately clears count
  a_async_reset_clears: assert property (@(negedge reset_n) ##0 (count == '0));

  // While in reset at a clk edge, count is 0
  a_reset_holds_zero:   assert property ( !reset_n |-> (count == '0) );

  // First active clock after reset release produces 1
  a_first_after_release: assert property ( $rose(reset_n) |-> (count == 'd1) );

  // When running (reset_n high in consecutive cycles), count increments modulo 2^WIDTH
  a_inc_modN: assert property ( reset_n && $past(reset_n) |-> (count == $past(count) + 1) );

  // No X/Z on count when out of reset
  a_no_x_count: assert property ( disable iff (!reset_n) !$isunknown(count) );

  // Optional: reset signal not X at sampling edges
  a_no_x_reset: assert property ( !$isunknown(reset_n) );

  // Coverage
  // See wrap-around from max to 0
  c_wrap: cover property ( reset_n && $past(reset_n) && ($past(count) == {WIDTH{1'b1}}) && (count == '0) );

  // See an async reset assertion
  c_reset_assert: cover property (@(negedge reset_n) 1'b1);

  // See reset release and first count = 1
  c_release_then_one: cover property ( $rose(reset_n) && (count == 'd1) );

endmodule

// Bind into DUT
bind up_counter up_counter_sva #(.WIDTH(4)) up_counter_sva_i (.clk(clk), .reset_n(reset_n), .count(count));