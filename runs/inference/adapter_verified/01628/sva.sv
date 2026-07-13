module debouncer_sva (
    input logic clk,
    input logic in,
    input logic out
);

// Stable input with no change keeps out stable on the next cycle.
    check_stable_no_change_keeps_out_stable: assert property (
        @(posedge clk) (state == STABLE && in == $past(in)) |=> (out == $past(out))
    );

// Stable input with a change moves to the unstable state.
    check_stable_change_moves_to_unstable: assert property (
        @(posedge clk) (state == STABLE && in != $past(in)) |=> (state == UNSTABLE)
    );

// Unstable with debounce_count at zero moves to the debounce state.
    check_unstable_zero_count_moves_to_debounce: assert property (
        @(posedge clk) (state == UNSTABLE && debounce_count == 0) |=> (state == DEBOUNCE)
    );

// Unstable with debounce_count non-zero decrements the counter.
    check_unstable_nonzero_count_decrements: assert property (
        @(posedge clk) (state == UNSTABLE && debounce_count != 0) |=> (debounce_count == $past(debounce_count) - 32'd1)
    );

// Unstable with debounce_count non-zero keeps out unchanged.
    check_unstable_nonzero_count_keeps_out: assert property (
        @(posedge clk) (state == UNSTABLE && debounce_count != 0) |=> (out == $past(out))
    );

// Debounce with no change moves to the stable state.
    check_debounce_no_change_moves_to_stable: assert property (
        @(posedge clk) (state == DEBOUNCE && in == $past(in)) |=> (state == STABLE)
    );

// Debounce with a change moves back to the unstable state.
    check_debounce_change_moves_to_unstable: assert property (
        @(posedge clk) (state == DEBOUNCE && in != $past(in)) |=> (state == UNSTABLE)
    );

// Debounce with a change resets the debounce counter.
    check_debounce_change_resets_count: assert property (
        @(posedge clk) (state == DEBOUNCE && in != $past(in)) |=> (debounce_count == debounce_time * clk_freq / 1000)
    );

// Debounce with a change updates out to the new input value.
    check_debounce_change_updates_out: assert property (
        @(posedge clk) (state == DEBOUNCE && in != $past(in)) |=> (out == in)
    );

endmodule
