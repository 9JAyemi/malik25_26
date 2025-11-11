// SVA for module adder
module adder_sva
(
  input              clk,
  input              rst,
  input      [31:0]  ain,
  input      [31:0]  bin,
  input      [31:0]  result,
  input      [31:0]  statistic,
  input      [31:0]  result_last
);

  default clocking cb @(posedge clk); endclocking

  // Guard for $past validity after reset deassertion
  logic past_valid;
  always @(posedge clk or posedge rst) begin
    if (rst) past_valid <= 1'b0;
    else     past_valid <= 1'b1;
  end

  // Reset behavior
  a_reset_result: assert property (rst |-> (result==32'h0 && result_last==32'h0));
  a_reset_stat:   assert property (rst |-> (statistic[31:16]==16'hc001 && statistic[15:0]==16'h0000));

  // Functional correctness
  a_add:   assert property (disable iff (rst) past_valid |-> result == $past(ain + bin));
  a_last:  assert property (disable iff (rst) past_valid |-> result_last == $past(result));

  // Derived invariant from the two-flop pipeline (pre-update view)
  a_eq_pre: assert property (disable iff (rst) result == result_last);

  // Statistic behavior
  a_stat_upper_const: assert property (disable iff (rst) (statistic[31:16]==16'hc001) and $stable(statistic[31:16]));
  a_stat_count_inc:   assert property (disable iff (rst) past_valid && (result != result_last)
                                       |-> statistic[15:0] == $past(statistic[15:0]) + 16'h1);
  a_stat_count_hold:  assert property (disable iff (rst) past_valid && (result == result_last)
                                       |-> statistic[15:0] == $past(statistic[15:0]));

  // X-propagation check after reset release
  a_no_x: assert property (disable iff (rst) past_valid |-> !$isunknown({result, statistic}));

  // Coverage
  c_reset_release:  cover property (rst ##1 !rst);
  c_result_changes: cover property (past_valid && $changed(result));
  c_stat_event:     cover property (past_valid && (result != result_last)
                                    && statistic[15:0] == $past(statistic[15:0]) + 16'h1);
  c_stat_wrap:      cover property (past_valid && (result != result_last)
                                    && $past(statistic[15:0]) == 16'hffff
                                    && statistic[15:0] == 16'h0000);
  c_add_overflow:   cover property (past_valid && (($past(ain) + $past(bin)) < $past(ain)));

endmodule

// Bind into DUT (including internal result_last)
bind adder adder_sva u_adder_sva (
  .clk       (clk),
  .rst       (rst),
  .ain       (ain),
  .bin       (bin),
  .result    (result),
  .statistic (statistic),
  .result_last(result_last)
);