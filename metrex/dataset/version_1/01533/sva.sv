// SVA for consecutive_ones_counter
// Bind this checker to the DUT

module consecutive_ones_counter_sva
(
  input clk,
  input reset,
  input [3:0] data,
  input [2:0] count,
  input [2:0] count_reg,
  input [2:0] count_next
);

  default clocking cb @(posedge clk); endclocking

  function automatic [2:0] f_lsb_ones (input [3:0] d);
    if (!d[0])       f_lsb_ones = 3'd0;
    else if (!d[1])  f_lsb_ones = 3'd1;
    else if (!d[2])  f_lsb_ones = 3'd2;
    else             f_lsb_ones = 3'd3;
  endfunction

  // Reset behavior
  assert property (reset |=> (count_reg == 3'd0 && count == 3'd0));
  assert property ((reset && $past(reset)) |-> (count_reg == 3'd0 && count == 3'd0));
  assert property ((!reset && $past(reset)) |-> (count_reg == 3'd0 && count == 3'd0));

  // Combinational next-state function
  assert property (@(*) count_next == f_lsb_ones(data));

  // Sequential update and output mirror
  assert property (!reset && !$past(reset) |-> count_reg == $past(count_next));
  assert property (count == count_reg);

  // End-to-end: one-cycle latency from data to count
  assert property (!reset && !$past(reset) |-> count == f_lsb_ones($past(data)));

  // Sanity/range
  assert property (count <= 3'd3);
  assert property (!$isunknown({count, count_reg}));

  // Functional coverage
  cover property (!reset && !$past(reset) && $past(data[0]) == 1'b0 |-> count == 3'd0);
  cover property (!reset && !$past(reset) && $past(data[0]) && !$past(data[1]) |-> count == 3'd1);
  cover property (!reset && !$past(reset) && (&$past(data[1:0])) && !$past(data[2]) |-> count == 3'd2);
  cover property (!reset && !$past(reset) && (&$past(data[2:0])) |-> count == 3'd3);
  cover property (reset ##1 !reset);

endmodule

bind consecutive_ones_counter consecutive_ones_counter_sva
(
  .clk(clk),
  .reset(reset),
  .data(data),
  .count(count),
  .count_reg(count_reg),
  .count_next(count_next)
);