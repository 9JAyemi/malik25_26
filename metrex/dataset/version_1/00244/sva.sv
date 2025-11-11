// SVA for counter. Bind to DUT for automatic checking.

module counter_sva (
  input logic       clk,
  input logic       rst,
  input logic [2:0] count
);
  default clocking @(posedge clk); endclocking

  // Safety checks
  a_rst_forces_zero: assert property (rst |-> count == 3'd0);
  a_no_x_on_count:   assert property (!$isunknown(count));

  // Functional checks (3-bit modulo-8 incrementer with synchronous reset)
  a_inc_mod8: assert property (!rst && !$isunknown($past(count)) |-> count == $past(count) + 3'd1);
  a_wrap_mod8: assert property (!rst && !$isunknown($past(count)) && $past(count) == 3'd7 |-> count == 3'd0);
  a_after_deassert_is_one: assert property ($fell(rst) |-> count == 3'd1);

  // Coverage
  c_full_cycle_no_reset: cover property (disable iff (rst)
      (count==3'd0) ##1 (count==3'd1) ##1 (count==3'd2) ##1 (count==3'd3) ##
      1 (count==3'd4) ##1 (count==3'd5) ##1 (count==3'd6) ##1 (count==3'd7) ##1 (count==3'd0)
  );
  c_wrap_observed: cover property (!rst && $past(!rst) && $past(count)==3'd7 && count==3'd0);
  c_reset_assert:  cover property (rst);
  c_reset_deassert:cover property ($fell(rst));
endmodule

bind counter counter_sva u_counter_sva (.clk(clk), .rst(rst), .count(count));