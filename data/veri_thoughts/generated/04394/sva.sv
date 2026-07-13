module sky130_fd_sc_ls__o211ai_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1
);

    // Y must be the NAND of B1, C1, and the OR of A1 and A2.
    check_function_equivalence: assert property (
        @($global_clock) Y == ~((A1 | A2) & B1 & C1)
    );

    // Y can be LOW only when B1, C1, and at least one A input are HIGH.
    check_low_only_when_all_terms_active: assert property (
        @($global_clock)
        (Y == 1'b0) |-> ((B1 == 1'b1) && (C1 == 1'b1) && ((A1 == 1'b1) || (A2 == 1'b1)))
    );

    // Y must be LOW when A1, B1, and C1 are all HIGH.
    check_low_when_a1_b1_c1_high: assert property (
        @($global_clock)
        ((A1 == 1'b1) && (B1 == 1'b1) && (C1 == 1'b1)) |-> (Y == 1'b0)
    );

    // Y must be LOW when A2, B1, and C1 are all HIGH.
    check_low_when_a2_b1_c1_high: assert property (
        @($global_clock)
        ((A2 == 1'b1) && (B1 == 1'b1) && (C1 == 1'b1)) |-> (Y == 1'b0)
    );

    // Y must be HIGH whenever B1 is LOW.
    check_high_when_b1_low: assert property (
        @($global_clock)
        (B1 == 1'b0) |-> (Y == 1'b1)
    );

    // Y must be HIGH whenever C1 is LOW.
    check_high_when_c1_low: assert property (
        @($global_clock)
        (C1 == 1'b0) |-> (Y == 1'b1)
    );

    // Y must be HIGH when both A inputs are LOW.
    check_high_when_a_inputs_low: assert property (
        @($global_clock)
        ((A1 == 1'b0) && (A2 == 1'b0)) |-> (Y == 1'b1)
    );

endmodule