module debouncer_sva #(
    parameter int clk_freq = 100000,
    parameter int debounce_time = 10
) (
    input logic clk,
    input logic in,
    input logic out,
    input logic [1:0] state,
    input logic [31:0] debounce_count
);

    localparam logic [1:0] STABLE   = 2'b00;
    localparam logic [1:0] UNSTABLE = 2'b01;
    localparam logic [1:0] DEBOUNCE = 2'b10;

    // STABLE with a mismatched input must transition to UNSTABLE.
    check_stable_mismatch_to_unstable: assert property (
        @(posedge clk) disable iff (1'b0)
        (state == STABLE && in != out) |=> (state == UNSTABLE)
    );

    // STABLE with a matched input must remain in STABLE.
    check_stable_match_stays_stable: assert property (
        @(posedge clk) disable iff (1'b0)
        (state == STABLE && in == out) |=> (state == STABLE)
    );

    // UNSTABLE with debounce_count at zero must transition to DEBOUNCE.
    check_unstable_zero_count_to_debounce: assert property (
        @(posedge clk) disable iff (1'b0)
        (state == UNSTABLE && debounce_count == 0) |=> (state == DEBOUNCE)
    );

    // UNSTABLE with debounce_count above zero must decrement and stay in UNSTABLE.
    check_unstable_nonzero_count_decrements: assert property (
        @(posedge clk) disable iff (1'b0)
        (state == UNSTABLE && debounce_count > 0) |=> (state == UNSTABLE && debounce_count == ($past(debounce_count) - 32'd1))
    );

    // DEBOUNCE with a mismatched input must transition back to UNSTABLE.
    check_debounce_mismatch_to_unstable: assert property (
        @(posedge clk) disable iff (1'b0)
        (state == DEBOUNCE && in != out) |=> (state == UNSTABLE)
    );

    // DEBOUNCE with a matched input must transition back to STABLE.
    check_debounce_match_to_stable: assert property (
        @(posedge clk) disable iff (1'b0)
        (state == DEBOUNCE && in == out) |=> (state == STABLE)
    );

    // UNSTABLE must drive out to the current input value.
    check_unstable_updates_out: assert property (
        @(posedge clk) disable iff (1'b0)
        (state == UNSTABLE) |-> (out == in)
    );

    // DEBOUNCE must not change out.
    check_debounce_holds_out: assert property (
        @(posedge clk) disable iff (1'b0)
        (state == DEBOUNCE) |-> (out == $past(out))
    );

    // STABLE must not change out.
    check_stable_holds_out: assert property (
        @(posedge clk) disable iff (1'b0)
        (state == STABLE) |-> (out == $past(out))
    );

    // UNSTABLE with debounce_count at zero must update out from the prior input.
    check_unstable_zero_count_updates_out: assert property (
        @(posedge clk) disable iff (1'b0)
        (state == UNSTABLE && debounce_count == 0) |=> (out == $past(in))
    );

endmodule