module ModmCountr_sva #(
    parameter int unsigned M = 50000000,
    parameter int unsigned N = ((M <= 1) ? 1 : $clog2(M))
) (
    input logic clk,
    input logic reset,
    input logic max_tick,
    input logic [N-1:0] q
);

    localparam logic [N-1:0] LAST_Q = M - 1;
    localparam logic [N-1:0] ONE_Q  = {{(N-1){1'b0}}, 1'b1};
    localparam bit RESET_TICK = (M == 1);

    // Reset clears the counter output to zero.
    check_reset_clears_count: assert property (
        @(posedge clk) reset |-> (q == '0)
    );

    // Reset drives max_tick consistently with the zero count.
    check_reset_max_tick_value: assert property (
        @(posedge clk) reset |-> (max_tick == RESET_TICK)
    );

    // max_tick is high exactly when q is at the terminal count.
    check_max_tick_matches_terminal_count: assert property (
        @(posedge clk) disable iff (reset)
        (max_tick == (q == LAST_Q))
    );

    // An in-range count remains in range on the next cycle.
    check_valid_count_stays_in_range: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && !$past(reset) && ($past(q) <= LAST_Q)) |-> (q <= LAST_Q)
    );

    // The counter wraps to zero after the terminal count.
    check_wrap_after_terminal_count: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && !$past(reset) && ($past(q) == LAST_Q)) |-> (q == '0)
    );

    // A zero count in normal operation must come from the terminal count.
    check_zero_only_after_terminal_count: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && !$past(reset) && ($past(q) <= LAST_Q) && (q == '0)) |-> ($past(q) == LAST_Q)
    );

    generate
        if (M > 1) begin : gen_m_gt_one
            // A non-terminal valid count increments by one.
            check_increment_before_terminal_count: assert property (
                @(posedge clk) disable iff (reset)
                (!$initstate && !$past(reset) && ($past(q) < LAST_Q)) |-> (q == ($past(q) + ONE_Q))
            );

            // The first cycle after reset deassertion starts at one.
            check_first_count_after_reset: assert property (
                @(posedge clk) disable iff (reset)
                (!$initstate && $past(reset)) |-> (q == ONE_Q)
            );

            // A zero count advances to one on the next cycle.
            check_zero_advances_to_one: assert property (
                @(posedge clk) disable iff (reset)
                (q == '0) |=> (q == ONE_Q)
            );

            // max_tick is a single-cycle pulse when M is greater than one.
            check_max_tick_is_single_cycle: assert property (
                @(posedge clk) disable iff (reset)
                max_tick |=> !max_tick
            );
        end
        else begin : gen_m_eq_one
            // For M equal to one, the first cycle after reset stays at zero with max_tick high.
            check_hold_zero_after_reset: assert property (
                @(posedge clk) disable iff (reset)
                (!$initstate && $past(reset)) |-> ((q == '0) && (max_tick == 1'b1))
            );
        end
    endgenerate

endmodule