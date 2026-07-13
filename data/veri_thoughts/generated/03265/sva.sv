module Debouncer_sva #(
    parameter int COUNT_MAX = 1000
) (
    input logic clk,
    input logic rst_n,
    input logic in,
    input logic out,
    input logic [9:0] count,
    input logic [1:0] state
);

    // Reset forces count, state, and output to zero.
    check_reset_values: assert property (
        @(posedge clk) !rst_n |-> (count == 10'd0 && state == 2'b00 && out == 1'b0)
    );

    // In idle, a matching input keeps the FSM in idle and preserves count.
    check_idle_match_stays_idle: assert property (
        @(posedge clk) disable iff (!rst_n)
        ($past(rst_n) && $past(state) == 2'b00 && $past(in) == $past(out))
        |-> (state == 2'b00 && count == $past(count) && out == $past(in))
    );

    // In idle, an input mismatch starts the wait state and clears count.
    check_idle_mismatch_starts_wait: assert property (
        @(posedge clk) disable iff (!rst_n)
        ($past(rst_n) && $past(state) == 2'b00 && $past(in) != $past(out))
        |-> (state == 2'b01 && count == 10'd0 && out == $past(out))
    );

    // In wait, count increments until the threshold is reached.
    check_wait_increments_count: assert property (
        @(posedge clk) disable iff (!rst_n)
        ($past(rst_n) && $past(state) == 2'b01 && $past(count) < COUNT_MAX)
        |-> (state == 2'b01 && count == ($past(count) + 10'd1) && out == $past(out))
    );

    // At the threshold, wait captures the input and moves to debounce state.
    check_wait_threshold_updates_output: assert property (
        @(posedge clk) disable iff (!rst_n)
        ($past(rst_n) && $past(state) == 2'b01 && $past(count) >= COUNT_MAX)
        |-> (state == 2'b10 && count == $past(count) && out == $past(in))
    );

    // The wait state never transitions directly back to idle.
    check_wait_never_goes_directly_idle: assert property (
        @(posedge clk) disable iff (!rst_n)
        ($past(rst_n) && $past(state) == 2'b01)
        |-> (state != 2'b00)
    );

    // In debounce, a new mismatch restarts the wait and clears count.
    check_debounce_mismatch_restarts_wait: assert property (
        @(posedge clk) disable iff (!rst_n)
        ($past(rst_n) && $past(state) == 2'b10 && $past(in) != $past(out))
        |-> (state == 2'b01 && count == 10'd0 && out == $past(out))
    );

    // In debounce, a stable input returns the FSM to idle.
    check_debounce_match_returns_idle: assert property (
        @(posedge clk) disable iff (!rst_n)
        ($past(rst_n) && $past(state) == 2'b10 && $past(in) == $past(out))
        |-> (state == 2'b00 && count == $past(count) && out == $past(out))
    );

    // The debounce state always exits on the next clock.
    check_debounce_exits_next_cycle: assert property (
        @(posedge clk) disable iff (!rst_n)
        ($past(rst_n) && $past(state) == 2'b10)
        |-> (state != 2'b10)
    );

    // Output changes only when wait has reached the threshold.
    check_output_changes_only_after_wait_threshold: assert property (
        @(posedge clk) disable iff (!rst_n)
        ($past(rst_n) && out != $past(out))
        |-> ($past(state) == 2'b01 && $past(count) >= COUNT_MAX && out == $past(in))
    );

endmodule