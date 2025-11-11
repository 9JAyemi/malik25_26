// SVA checker for pcie_7x_v1_3_fast_cfg_init_cntr
module pcie_7x_v1_3_fast_cfg_init_cntr_sva #(
  parameter int PATTERN_WIDTH = 8,
  parameter     INIT_PATTERN  = 8'hA5
)(
  input                          clk,
  input                          rst,
  input      [PATTERN_WIDTH-1:0] pattern_o
);

  default clocking cb @(posedge clk); endclocking

  // Track that we've observed at least one synchronous reset
  bit seen_reset;
  initial seen_reset = 1'b0;
  always_ff @(posedge clk) if (rst) seen_reset <= 1'b1;

  // Reset drives output to 0 and is known
  a_reset_clears: assert property (rst |-> pattern_o == '0);
  a_no_x_on_reset: assert property (rst |-> !$isunknown(pattern_o));

  // While running (after a reset has been seen and rst deasserted):
  // - no X/Z
  a_no_x_running: assert property (disable iff (!seen_reset || rst)
                                   !$isunknown(pattern_o));

  // - monotonic non-decreasing
  a_monotonic: assert property (disable iff (!seen_reset || rst)
                                (!$isunknown($past(pattern_o))) |-> pattern_o >= $past(pattern_o));

  // - increment by 1 until INIT_PATTERN
  a_step_until_target: assert property (disable iff (!seen_reset || rst)
                                        (!$isunknown($past(pattern_o)) && $past(pattern_o) != INIT_PATTERN)
                                        |-> pattern_o == $past(pattern_o) + 1);

  // - hold once INIT_PATTERN reached (saturating behavior)
  a_hold_at_target: assert property (disable iff (!seen_reset || rst)
                                     (!$isunknown($past(pattern_o)) && $past(pattern_o) == INIT_PATTERN)
                                     |-> $stable(pattern_o));

  // - never exceed INIT_PATTERN after reset has been observed
  a_never_exceed_target: assert property (disable iff (!seen_reset)
                                          !rst |-> pattern_o <= INIT_PATTERN);

  // Functional coverage

  // Cover reaching the target value after a deassertion of reset within the expected bound
  c_reach_target_bounded: cover property (
    seen_reset && $fell(rst) ##[0:INIT_PATTERN] (pattern_o == INIT_PATTERN)
  );

  // Cover that once at target, it holds for multiple cycles
  c_hold_target: cover property (disable iff (rst)
                                 pattern_o == INIT_PATTERN ##1 $stable(pattern_o)[*3]);

endmodule

// Bind into DUT
bind pcie_7x_v1_3_fast_cfg_init_cntr
  pcie_7x_v1_3_fast_cfg_init_cntr_sva #(
    .PATTERN_WIDTH(PATTERN_WIDTH),
    .INIT_PATTERN (INIT_PATTERN)
  ) pcie_7x_v1_3_fast_cfg_init_cntr_sva_i (
    .clk(clk),
    .rst(rst),
    .pattern_o(pattern_o)
  );