// SVA for counter
module counter_sva (
  input logic        clk,
  input logic        reset,
  input logic        enable,
  input logic [1:0]  count
);

  default clocking cb @(posedge clk); endclocking

  bit past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // Sanity: known values
  a_inputs_known: assert property (past_valid |-> !$isunknown({reset, enable}));
  a_count_known : assert property (past_valid |-> !$isunknown(count));

  // Reset behavior
  a_reset_clears: assert property (reset |=> count == 2'd0);

  // Next-state function (hold vs increment; modulo-4 implied by 2-bit width)
  a_next_state: assert property (
    past_valid && !reset |=> ($past(enable) ? (count == $past(count) + 2'd1)
                                            : (count == $past(count)))
  );

  // Count only changes due to prior enable or prior reset
  a_change_guard: assert property (
    past_valid && (count != $past(count)) |-> ($past(enable) || $past(reset))
  );

  // Coverage
  c_seen_reset : cover property (reset);
  c_state_0    : cover property (!reset && count == 2'd0);
  c_state_1    : cover property (!reset && count == 2'd1);
  c_state_2    : cover property (!reset && count == 2'd2);
  c_state_3    : cover property (!reset && count == 2'd3);
  c_increment  : cover property (past_valid && !reset && $past(!reset) && $past(enable)
                                 |=> count == $past(count) + 2'd1);
  c_hold       : cover property (past_valid && !reset && $past(!reset) && !$past(enable)
                                 |=> count == $past(count));
  c_wrap       : cover property (past_valid && !reset && $past(!reset) &&
                                 $past(enable) && $past(count) == 2'd3
                                 |=> count == 2'd0);

endmodule

// Bind into DUT
bind counter counter_sva counter_sva_i(.clk(clk), .reset(reset), .enable(enable), .count(count));