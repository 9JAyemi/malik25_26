// SVA for binary_counter
module binary_counter_sva (
  input logic        clk,
  input logic        reset,
  input logic [3:0]  count,
  input logic [3:0]  temp_count
);

  // Sanity
  a_no_x:        assert property (@(posedge clk) !$isunknown({reset, count}));
  a_out_mirror:  assert property (@(posedge clk) count == temp_count);
  a_in_range:    assert property (@(posedge clk) count <= 4'd7);

  // Reset behavior
  a_reset_to_zero: assert property (@(posedge clk) reset |=> count == 4'd0);

  // Next-state function (when not in reset)
  a_inc:  assert property (@(posedge clk) disable iff (reset)
                           (count < 4'd7) |=> count == $past(count) + 1);
  a_wrap: assert property (@(posedge clk) disable iff (reset)
                           (count == 4'd7) |=> count == 4'd0);

  // Coverage
  c_full_cycle: cover property (@(posedge clk) disable iff (reset)
                                count==4'd0 ##1 1 ##1 2 ##1 3 ##1 4 ##1 5 ##1 6 ##1 7 ##1 0);
  c_reset_assert:  cover property (@(posedge clk) $rose(reset));
  c_reset_release: cover property (@(posedge clk) $fell(reset));
  c_wrap_event:    cover property (@(posedge clk) disable iff (reset)
                                   $past(count)==4'd7 && count==4'd0);
endmodule

bind binary_counter binary_counter_sva u_binary_counter_sva (
  .clk(clk),
  .reset(reset),
  .count(count),
  .temp_count(temp_count)
);