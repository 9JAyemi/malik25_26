// SVA checker for binary_counter
module binary_counter_sva #(parameter int N = 4)
(
  input logic              clk,
  input logic              reset,
  input logic [N-1:0]      count
);

  localparam logic [N-1:0] MAX = {N{1'b1}};

  default clocking cb @(posedge clk); endclocking

  // Sanity: no X/Z on key signals at sampling edges
  a_no_x:           assert property (!$isunknown({reset, count}));

  // When reset is asserted, count must be 0 every cycle
  a_reset_zero:     assert property (reset |-> (count == '0));

  // First cycle after reset deasserts: increment from previous (0) by 1
  a_step_after_rst: assert property ($past(reset) && !reset |-> count == $past(count) + 1);

  // While running (no reset in back-to-back cycles): strict +1 modulo 2^N
  a_inc_running:    assert property (!reset && $past(!reset) |-> count == $past(count) + 1);

  // Explicit wrap check from MAX to 0 when running
  a_wrap:           assert property (!reset && $past(!reset) && $past(count) == MAX |-> count == '0);

  // Coverage
  c_seen_reset:     cover  property (reset);
  c_exit_reset:     cover  property ($past(reset) && !reset);
  c_reach_max:      cover  property ($past(reset) && !reset ##[0:$] (count == MAX));
  c_rollover:       cover  property (!reset && $past(!reset) && $past(count) == MAX && count == '0);

endmodule

// Bind example:
// bind binary_counter binary_counter_sva #(.N(N)) i_binary_counter_sva (.*);