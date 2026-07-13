module WcaDspStrobe_sva #(
    parameter logic [23:0] INITIAL_VAL   = 24'd0,
    parameter logic [23:0] INCREMENT_VAL = 24'h1
) (
    input logic        clock,
    input logic        reset,
    input logic        strobe_in,
    input logic        enable,
    input logic [23:0] rate,
    input logic        strobe_out,
    input logic [23:0] count
);

    // strobe_out is the combinational compare of count and rate.
    check_strobe_out_matches_count_rate: assert property (
        @(posedge clock) disable iff (reset)
        (strobe_out == (count == rate))
    );

    // After reset is released, count remains at the reset value.
    check_count_initial_after_reset_release: assert property (
        @(posedge clock) disable iff (reset)
        $fell(reset) |-> (count == INITIAL_VAL)
    );

    // Disabling the block clears count on the next cycle.
    check_count_resets_when_disabled: assert property (
        @(posedge clock) disable iff (reset)
        !enable |=> (count == INITIAL_VAL)
    );

    // A compare hit clears count on the next cycle.
    check_count_resets_when_count_hits_rate: assert property (
        @(posedge clock) disable iff (reset)
        (count == rate) |=> (count == INITIAL_VAL)
    );

    // A high strobe_out clears count on the next cycle.
    check_count_resets_on_strobe_out: assert property (
        @(posedge clock) disable iff (reset)
        strobe_out |=> (count == INITIAL_VAL)
    );

    // A qualified strobe_in increments count by INCREMENT_VAL.
    check_count_increments_on_strobe_in: assert property (
        @(posedge clock) disable iff (reset)
        enable && !strobe_out && strobe_in |=> (count == ($past(count) + INCREMENT_VAL))
    );

    // Without strobe_in, count holds when enabled and below rate.
    check_count_holds_without_strobe_in: assert property (
        @(posedge clock) disable iff (reset)
        enable && !strobe_out && !strobe_in |=> (count == $past(count))
    );

endmodule