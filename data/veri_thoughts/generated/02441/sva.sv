module fsm_3bit_binary_counter_sva (
  input logic clk,
  input logic reset,
  input logic [2:0] count
);
  // Clock: clk (posedge). Reset: reset (active-low, async). Sequential FSM cycling A->B->C->A. Count mirrors state.

  localparam logic [2:0] A = 3'b000;
  localparam logic [2:0] B = 3'b001;
  localparam logic [2:0] C = 3'b010;

  ///// Reset behavior /////
  // While reset is asserted low, count is forced to A.
  reset_forces_A: assert property (
    @(posedge clk) (reset == 1'b0) |-> (count == A)
  );

  // While reset is asserted low, MSB of count stays 0.
  msb_zero_in_reset: assert property (
    @(posedge clk) (reset == 1'b0) |-> (count[2] == 1'b0)
  );

  ///// Legal values and X-checks when active /////
  // When not in reset, count only takes A, B, or C.
  active_values_restricted: assert property (
    @(posedge clk) disable iff (!reset) (count inside {A, B, C})
  );

  // When not in reset, count has no X/Z bits.
  no_x_on_count_active: assert property (
    @(posedge clk) disable iff (!reset) !$isunknown(count)
  );

  // When not in reset, count[2] is always 0.
  msb_zero_active: assert property (
    @(posedge clk) disable iff (!reset) (count[2] == 1'b0)
  );

  ///// Step-by-step sequencing /////
  // From A, next value is B (when previous cycle also active).
  step_A_to_B: assert property (
    @(posedge clk) disable iff (!reset) ($past(reset) && $past(count) == A) |-> (count == B)
  );

  // From B, next value is C (when previous cycle also active).
  step_B_to_C: assert property (
    @(posedge clk) disable iff (!reset) ($past(reset) && $past(count) == B) |-> (count == C)
  );

  // From C, next value is A (when previous cycle also active).
  step_C_to_A: assert property (
    @(posedge clk) disable iff (!reset) ($past(reset) && $past(count) == C) |-> (count == A)
  );

  // When continuously active, count changes every cycle (no self-loop).
  count_changes_each_active_cycle: assert property (
    @(posedge clk) disable iff (!reset) $past(reset) |-> (count != $past(count))
  );

  ///// Multi-cycle sequencing /////
  // Starting at A, the next two steps are B then C, then back to A.
  period_three_from_A: assert property (
    @(posedge clk) disable iff (!reset) (count == A) |-> ##1 (count == B) ##1 (count == C) ##1 (count == A)
  );

endmodule