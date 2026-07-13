module abs_difference_sva (
    input logic CLOCK,
    input logic RESET,
    input logic [11:0] x,
    input logic [11:0] y,
    input logic [11:0] DIFF
);
    // Clock: CLOCK (posedge). Reset: RESET (active-high, asynchronous).
    // Logic: Sequential register computing absolute difference; DIFF cleared to 0 on RESET.

    // DIFF must be 0 whenever RESET is asserted at the clock edge.
    reset_forces_zero: assert property (
        @(posedge CLOCK) RESET |-> (DIFF == 12'd0)
    );

    // Functional behavior: when not in reset, DIFF equals |x - y|.
    diff_matches_abs: assert property (
        @(posedge CLOCK) disable iff (RESET) DIFF == ((x > y) ? (x - y) : (y - x))
    );

    // If inputs are equal (not in reset), DIFF must be 0.
    diff_zero_when_equal: assert property (
        @(posedge CLOCK) disable iff (RESET) (x == y) |-> (DIFF == 12'd0)
    );

    // If inputs differ (not in reset), DIFF must be strictly positive.
    diff_positive_when_unequal: assert property (
        @(posedge CLOCK) disable iff (RESET) (x != y) |-> (DIFF > 12'd0)
    );

    // DIFF never exceeds the larger of x and y when not in reset.
    diff_bounded_by_max: assert property (
        @(posedge CLOCK) disable iff (RESET) (DIFF <= ((x > y) ? x : y))
    );

    // DIFF plus the smaller input equals the larger input when not in reset.
    add_inverse_relation: assert property (
        @(posedge CLOCK) disable iff (RESET) ((x > y) ? ((DIFF + y) == x) : ((DIFF + x) == y))
    );
endmodule