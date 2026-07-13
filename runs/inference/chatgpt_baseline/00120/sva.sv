module sky130_fd_sc_ms__a2111oi_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1,
    input logic D1,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // No RTL clock or reset exists; sample this combinational cell on $global_clock.
    // The RTL is purely combinational; Y reduces to a 2-of-3 function of B1, C1, and D1.

    // Y must match the implemented combinational function.
    check_y_matches_function: assert property (
        @($global_clock)
        Y == ((B1 & C1) | (B1 & D1) | (C1 & D1))
    );

    // If B1 and C1 are high, Y must be high.
    check_y_high_when_b1_c1_high: assert property (
        @($global_clock)
        (B1 & C1) |-> Y
    );

    // If B1 and D1 are high, Y must be high.
    check_y_high_when_b1_d1_high: assert property (
        @($global_clock)
        (B1 & D1) |-> Y
    );

    // If C1 and D1 are high, Y must be high.
    check_y_high_when_c1_d1_high: assert property (
        @($global_clock)
        (C1 & D1) |-> Y
    );

    // If B1 and C1 are both low, Y must be low.
    check_y_low_when_b1_c1_low: assert property (
        @($global_clock)
        (~B1 & ~C1) |-> ~Y
    );

    // If B1 and D1 are both low, Y must be low.
    check_y_low_when_b1_d1_low: assert property (
        @($global_clock)
        (~B1 & ~D1) |-> ~Y
    );

    // If C1 and D1 are both low, Y must be low.
    check_y_low_when_c1_d1_low: assert property (
        @($global_clock)
        (~C1 & ~D1) |-> ~Y
    );

endmodule