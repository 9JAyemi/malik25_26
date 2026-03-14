module sky130_fd_sc_lp__a22oi_1_sva (
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic Y
);
    // Y equals (A1 & A2) | (B1 & B2).
    check_function_definition: assert property (
        @($global_clock) Y == ((A1 & A2) | (B1 & B2))
    );

    // If Y is HIGH, at least one pair (A1&A2) or (B1&B2) is HIGH.
    check_y_high_implies_pair_true: assert property (
        @($global_clock) Y |-> ((A1 & A2) | (B1 & B2))
    );

    // If A1&A2 is HIGH, Y must be HIGH.
    check_pair_a_implies_y: assert property (
        @($global_clock) (A1 & A2) |-> Y
    );

    // If B1&B2 is HIGH, Y must be HIGH.
    check_pair_b_implies_y: assert property (
        @($global_clock) (B1 & B2) |-> Y
    );

    // If neither pair is HIGH, Y must be LOW.
    check_neither_pair_implies_y_low: assert property (
        @($global_clock) (!(A1 & A2) && !(B1 & B2)) |-> (Y == 1'b0)
    );

    // If A1 and B1 are both LOW, Y must be LOW.
    check_a1_b1_zero_implies_y_zero: assert property (
        @($global_clock) (!A1 && !B1) |-> (Y == 1'b0)
    );

    // If A2 and B2 are both LOW, Y must be LOW.
    check_a2_b2_zero_implies_y_zero: assert property (
        @($global_clock) (!A2 && !B2) |-> (Y == 1'b0)
    );

    // If A1 and A2 are LOW, Y equals (B1 & B2).
    check_apair_zero_reduces_to_bterm: assert property (
        @($global_clock) (!A1 && !A2) |-> (Y == (B1 & B2))
    );

    // If B1 and B2 are LOW, Y equals (A1 & A2).
    check_bpair_zero_reduces_to_aterm: assert property (
        @($global_clock) (!B1 && !B2) |-> (Y == (A1 & A2))
    );

    // If Y is LOW, neither (A1&A2) nor (B1&B2) is HIGH.
    check_y_low_implies_no_pair_true: assert property (
        @($global_clock) (Y == 1'b0) |-> (!(A1 & A2) && !(B1 & B2))
    );
endmodule