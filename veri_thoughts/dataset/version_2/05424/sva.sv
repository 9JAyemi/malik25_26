module Problem1_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic X,
    input logic Y
);

    // X must be high whenever A and C are both high.
    check_x_ac_high: assert property (
        @($global_clock)
        ((A & C) == 1'b1) |-> (X == 1'b1)
    );

    // X must be high whenever B and D are not both high.
    check_x_bd_not_both_high: assert property (
        @($global_clock)
        ((B & D) == 1'b0) |-> (X == 1'b1)
    );

    // X is low only when B and D are high and A and C are not both high.
    check_x_only_low_case: assert property (
        @($global_clock)
        (((A & C) == 1'b0) && ((B & D) == 1'b1)) |-> (X == 1'b0)
    );

    // Y must be high whenever A and ~C are not both high.
    check_y_primary_case: assert property (
        @($global_clock)
        ((A & (~C)) == 1'b0) |-> (Y == 1'b1)
    );

    // Y must be high in the remaining case when D is high.
    check_y_remaining_case_d_high: assert property (
        @($global_clock)
        (((A & (~C)) == 1'b1) && (D == 1'b1)) |-> (Y == 1'b1)
    );

    // Y is low only when A is high, C is low, and D is low.
    check_y_only_low_case: assert property (
        @($global_clock)
        (((A & (~C)) == 1'b1) && (D == 1'b0)) |-> (Y == 1'b0)
    );

endmodule