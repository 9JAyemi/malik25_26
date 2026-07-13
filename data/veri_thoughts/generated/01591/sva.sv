module debouncer_sva #(
    parameter int unsigned debounce_time = 10
) (
    input logic clock,
    input logic signal_in,
    input logic signal_out,
    input logic [debounce_time-1:0] stable_count
);
    // Clock: posedge clock; no reset present; sequential logic only.

    // Output is always the previous cycle's input (one-cycle latency).
    check_out_follows_prev_in: assert property (
        @(posedge clock) $past(1'b1) |-> (signal_out == $past(signal_in))
    );

    // When input and output differ, next cycle output equals prior input and counter resets.
    check_mismatch_updates_out_and_resets_count: assert property (
        @(posedge clock) (signal_in != signal_out) |-> ##1 ((signal_out == $past(signal_in)) && (stable_count == '0))
    );

    // When input equals output and threshold not reached, counter increments by 1 next cycle.
    check_equal_not_thresh_increments_count: assert property (
        @(posedge clock) (signal_in == signal_out) && (stable_count != debounce_time) |-> ##1 (stable_count == $past(stable_count) + 1)
    );

    // When input equals output and threshold reached, counter resets next cycle.
    check_equal_thresh_resets_count: assert property (
        @(posedge clock) (signal_in == signal_out) && (stable_count == debounce_time) |-> ##1 (stable_count == '0)
    );

    // When input equals output and threshold not reached, output holds its value next cycle.
    check_equal_not_thresh_holds_out: assert property (
        @(posedge clock) (signal_in == signal_out) && (stable_count != debounce_time) |-> ##1 (signal_out == $past(signal_out))
    );

    // When input equals output and threshold reached, output still holds its value next cycle.
    check_equal_thresh_holds_out: assert property (
        @(posedge clock) (signal_in == signal_out) && (stable_count == debounce_time) |-> ##1 (signal_out == $past(signal_out))
    );

    // If counter is non-zero, previous cycle had input equal to output.
    check_count_nonzero_prev_equal: assert property (
        @(posedge clock) ($past(1'b1) && (stable_count != '0)) |-> ($past(signal_in) == $past(signal_out))
    );

    // On any cycle with input equal to output, next counter is either incremented or reset.
    check_equal_count_update_only_inc_or_zero: assert property (
        @(posedge clock) (signal_in == signal_out) |-> ##1 ((stable_count == '0) || (stable_count == $past(stable_count) + 1))
    );
endmodule