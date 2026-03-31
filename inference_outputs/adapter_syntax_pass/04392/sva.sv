module my_module_sva (
    input logic [1:0] A1,
    input logic [1:0] A2,
    input logic [1:0] B1,
    input logic [1:0] B2,
    input logic [1:0] C1,
    input logic [1:0] VPWR,
    input logic [1:0] VGND,
    input logic [1:0] VPB,
    input logic [1:0] VNB,
    input logic X
);

    // X must match the implemented A1/A2/B1/B2 comparison.
    check_x_matches_ab_compare: assert property (
        @($global_clock) X == ((A1 == B1) && (A2 == B2))
    );

    // When C1 is not VPWR, X must pass through the A1/A2/B1/B2 comparison.
    check_x_passthrough_when_c1_not_vpwr: assert property (
        @($global_clock) (C1 != VPWR) |-> (X == ((A1 == B1) && (A2 == B2)))
    );

    // When C1 is VPWR, X must be inverted relative to the A1/A2/B1/B2 comparison.
    check_x_inverted_when_c1_vpwr: assert property (
        @($global_clock) (C1 == VPWR) |-> (X == ~((A1 == B1) && (A2 == B2)))
    );

    // With C1 not VPWR, a mismatched A1/B1 pair must drive X low.
    check_x_low_when_a1_ne_b1: assert property (
        @($global_clock) ((C1 != VPWR) && (A1 != B1)) |-> (X == 1'b0)
    );

    // With C1 not VPWR, a mismatched A2/B2 pair must drive X low.
    check_x_low_when_a2_ne_b2: assert property (
        @($global_clock) ((C1 != VPWR) && (A2 != B2)) |-> (X == 1'b0)
    );

    // With C1 not VPWR, a matching A1/B1 and A2/B2 pair must drive X high.
    check_x_high_when_ab_match: assert property (
        @($global_clock) ((C1 != VPWR) && (A1 == B1) && (A2 == B2)) |-> (X == 1'b1)
    );

    // With C1 VPWR, a mismatched A1/B1 pair must drive X high.
    check_x_high_when_a1_ne_b1_vpwr: assert property (
        @($global_clock) ((C1 == VPWR) && (A1 != B1)) |-> (X == 1'b1)
    );

    // With C1 VPWR, a mismatched A2/B2 pair must drive X high.
    check_x_high_when_a2_ne_b2_vpwr: assert property (
        @($global_clock) ((C1 == VPWR) && (A2 != B2)) |-> (X == 1'b1)
    );

    // With C1 VPWR, a matching A1/B1 and A2/B2 pair must drive X low.
    check_x_low_when_ab_match_vpwr: assert property (
        @($global_clock) ((C1 == VPWR) && (A1 == B1) && (A2 == B2)) |-> (X == 1'b0)
    );

endmodule