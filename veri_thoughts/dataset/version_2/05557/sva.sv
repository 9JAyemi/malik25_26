module my_module_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2
);

    // Check the implemented combinational equation for Y.
    check_y_boolean_function: assert property (
        @($global_clock)
        Y == ((~(A1 & A2)) & (~(B1 & B2)))
    );

    // If A1 and A2 are both high, Y must be low.
    check_a_pair_high_forces_y_low: assert property (
        @($global_clock)
        (A1 && A2) |-> (Y == 1'b0)
    );

    // If B1 and B2 are both high, Y must be low.
    check_b_pair_high_forces_y_low: assert property (
        @($global_clock)
        (B1 && B2) |-> (Y == 1'b0)
    );

    // If neither input pair is simultaneously high, Y must be high.
    check_no_pair_high_forces_y_high: assert property (
        @($global_clock)
        (!(A1 && A2) && !(B1 && B2)) |-> (Y == 1'b1)
    );

    // Y high means A1 and A2 are not both high.
    check_y_high_excludes_a_pair_high: assert property (
        @($global_clock)
        (Y == 1'b1) |-> !(A1 && A2)
    );

    // Y high means B1 and B2 are not both high.
    check_y_high_excludes_b_pair_high: assert property (
        @($global_clock)
        (Y == 1'b1) |-> !(B1 && B2)
    );

    // Y low requires at least one input pair to be simultaneously high.
    check_y_low_requires_asserted_pair: assert property (
        @($global_clock)
        (Y == 1'b0) |-> ((A1 && A2) || (B1 && B2))
    );

endmodule