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

    // When C1 is not VPWR, X must pass through the implemented comparison result.
    check_x_passthrough_when_c1_not_vpwr: assert property (
        @($global_clock) (C1 != VPWR) |-> (X == ((A1 == B1) && (A2 == B2)))
    );

    // When C1 is VPWR and VPB equals VGND, X must invert the implemented comparison result.
    check_x_inverts_when_c1_vpwr_and_vpb_eq_vgnd: assert property (
        @($global_clock) ((C1 == VPWR) && (VPB == VGND)) |-> (X == ~((A1 == B1) && (A2 == B2)))
    );

    // When C1 is VPWR and VPB differs from VGND, X must pass through the implemented comparison result.
    check_x_passthrough_when_c1_vpwr_and_vpb_ne_vgnd: assert property (
        @($global_clock) ((C1 == VPWR) && (VPB != VGND)) |-> (X == ((A1 == B1) && (A2 == B2)))
    );

    // With C1 not VPWR and equal A1/B1 and A2/B2, X must be high.
    check_x_high_when_c1_not_vpwr_and_ab_equal: assert property (
        @($global_clock) ((C1 != VPWR) && (A1 == B1) && (A2 == B2)) |-> (X == 1'b1)
    );

    // With C1 not VPWR and any A1/B1 or A2/B2 mismatch, X must be low.
    check_x_low_when_c1_not_vpwr_and_ab_mismatch: assert property (
        @($global_clock) ((C1 != VPWR) && ((A1 != B1) || (A2 != B2))) |-> (X == 1'b0)
    );

    // With C1 VPWR, VPB equals VGND, and equal A1/B1 and A2/B2, X must be low.
    check_x_low_when_c1_vpwr_vpb_eq_vgnd_and_ab_equal: assert property (
        @($global_clock) ((C1 == VPWR) && (VPB == VGND) && (A1 == B1) && (A2 == B2)) |-> (X == 1'b0)
    );

    // With C1 VPWR, VPB equals VGND, and any A1/B1 or A2/B2 mismatch, X must be high.
    check_x_high_when_c1_vpwr_vpb_eq_vgnd_and_ab_mismatch: assert property (
        @($global_clock) ((C1 == VPWR) && (VPB == VGND) && ((A1 != B1) || (A2 != B2))) |-> (X == 1'b1)
    );

endmodule