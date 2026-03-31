module digital_circuit_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1_N,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // Y matches the exact combinational equation implemented in the RTL.
    check_y_matches_rtl_equation: assert property (
        @($global_clock)
        Y == (((A1 & A2) | (VPWR & !VGND & !A1 & A2) | (!VPWR & VGND & A1 & !A2)) & !B1_N & !(VGND & VPB & VNB))
    );

    // B1_N high forces the output low.
    check_b1n_high_forces_y_low: assert property (
        @($global_clock)
        B1_N |-> !Y
    );

    // VGND high with VPB and VNB high forces the output low.
    check_vgnd_with_vpb_vnb_high_forces_y_low: assert property (
        @($global_clock)
        (VGND & VPB & VNB) |-> !Y
    );

    // With B1_N low and VGND low, Y reduces to A1 & A2.
    check_no_b1n_and_no_vgnd_reduces_to_a1_and_a2: assert property (
        @($global_clock)
        (!B1_N && !VGND) |-> (Y == (A1 & A2))
    );

    // With B1_N low and A1 low, Y must be low.
    check_no_a1_forces_y_low: assert property (
        @($global_clock)
        (!B1_N && !A1) |-> !Y
    );

    // With B1_N low and A2 low, Y must be low.
    check_no_a2_forces_y_low: assert property (
        @($global_clock)
        (!B1_N && !A2) |-> !Y
    );

    // With B1_N low and A1 high, Y reduces to A2.
    check_no_b1n_and_a1_high_reduces_to_a2: assert property (
        @($global_clock)
        (!B1_N && A1) |-> (Y == A2)
    );

    // With B1_N low and A2 high, Y reduces to A1.
    check_no_b1n_and_a2_high_reduces_to_a1: assert property (
        @($global_clock)
        (!B1_N && A2) |-> (Y == A1)
    );

    // With B1_N low and A1 equal to A2, Y must be high.
    check_equal_a1_a2_sets_y_high: assert property (
        @($global_clock)
        (!B1_N && (A1 == A2)) |-> Y
    );

    // With B1_N low and A1 different from A2, Y must be low.
    check_unequal_a1_a2_clears_y_low: assert property (
        @($global_clock)
        (!B1_N && (A1 != A2)) |-> !Y
    );

endmodule