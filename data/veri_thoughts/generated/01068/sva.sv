module ring_counter_sva #(
  parameter int n = 4
) (
  input  logic             clk,
  input  logic [n-1:0]     out,
  input  logic [n-1:0]     state
);
  // Clock: clk; Reset: none. Sequential counter with special wrap/reset; combinational out from state.
  localparam logic [n-1:0] ALL_ZEROS = {n{1'b0}};
  localparam logic [n-1:0] ALL_ONES  = {n{1'b1}};

  // When state equals n, next state must be 0.
  check_state_reset_on_n: assert property (
    @(posedge clk) disable iff ($initstate)
    (state == n) |=> (state == ALL_ZEROS)
  );

  // When state equals all ones, next state wraps to 0.
  check_state_wrap_from_all_ones: assert property (
    @(posedge clk) disable iff ($initstate)
    (state == ALL_ONES) |=> (state == ALL_ZEROS)
  );

  // When state is not n, next state increments by 1 (mod 2^n).
  check_state_increments_when_not_n: assert property (
    @(posedge clk) disable iff ($initstate)
    (state != n) |=> (state == ($past(state) + 1))
  );

  // A next-state of 0 arises only from prior state n or all ones.
  check_zero_next_only_from_prev_n_or_all_ones: assert property (
    @(posedge clk) disable iff ($initstate)
    (state == ALL_ZEROS) |-> (($past(state) == n) || ($past(state) == ALL_ONES))
  );

  // When state is all ones, out must be all ones.
  check_out_all_ones_when_state_all_ones: assert property (
    @(posedge clk)
    (state == ALL_ONES) |-> (out == ALL_ONES)
  );

  // If state < n, out is exactly one-hot at position state.
  check_out_onehot_when_state_lt_n: assert property (
    @(posedge clk)
    (state < n) |-> ($onehot(out) && (out == (1 << state)))
  );

  // If state >= n and not all ones, out must be zero.
  check_out_zero_when_state_ge_n_not_all_ones: assert property (
    @(posedge clk)
    ((state >= n) && (state != ALL_ONES)) |-> (out == ALL_ZEROS)
  );

  // out can be all ones only when state is all ones.
  check_out_allones_implies_state_allones: assert property (
    @(posedge clk)
    (out == ALL_ONES) |-> (state == ALL_ONES)
  );

  // State value n cannot persist for two consecutive cycles.
  check_state_n_not_sticky: assert property (
    @(posedge clk) disable iff ($initstate)
    (state == n) |=> (state != n)
  );

  // For n>1, when state equals n, out must be zero (truncation of 1<<n).
  generate if (n > 1) begin : gen_n_gt1
    check_out_zero_when_state_eq_n_n_gt1: assert property (
      @(posedge clk)
      (state == n) |-> (out == ALL_ZEROS)
    );
  end endgenerate

  // For n>1, when state == n-1, next state must be n.
  generate if (n > 1) begin : gen_n_minus1_to_n
    check_state_n_minus1_goto_n: assert property (
      @(posedge clk) disable iff ($initstate)
      (state == (n-1)) |=> (state == n)
    );
  end endgenerate

endmodule