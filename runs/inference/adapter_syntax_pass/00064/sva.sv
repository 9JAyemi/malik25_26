module and_gate_sva (
    input logic A1,
    input logic A2,
    input logic B1,
    input logic VPWR,
    input logic X,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // X must equal the AND of A1, A2, B1, and VPWR.
    check_x_matches_and_function: assert property (
        @($global_clock) X == (A1 & A2 & B1 & VPWR)
    );

    // X must be high when all four AND inputs are high.
    check_x_high_when_all_inputs_high: assert property (
        @($global_clock) (A1 & A2 & B1 & VPWR) |-> X
    );

    // X must be low when A1 is low.
    check_x_low_when_a1_low: assert property (
        @($global_clock) !A1 |-> !X
    );

    // X must be low when A2 is low.
    check_x_low_when_a2_low: assert property (
        @($global_clock) !A2 |-> !X
    );

    // X must be low when B1 is low.
    check_x_low_when_b1_low: assert property (
        @($global_clock) !B1 |-> !X
    );

    // X must be low when VPWR is low.
    check_x_low_when_vpwr_low: assert property (
        @($global_clock) !VPWR |-> !X
    );

    // VGND, VPB, and VNB do not affect X when the AND inputs are stable.
    check_x_ignores_unused_power_pins: assert property (
        @($global_clock)
        ($stable(A1) && $stable(A2) && $stable(B1) && $stable(VPWR)) |-> $stable(X)
    );

endmodule