module logic_circuit_sva (
    input logic X,
    input logic A,
    input logic VPWR,
    input logic VGND,
    input logic VNB,
    input logic VPB
);

    // No RTL clock or reset; use $global_clock for combinational checking.

    // X depends only on A, VPWR, and VGND as implemented.
    check_output_function: assert property (
        @($global_clock) X == (A & VPWR & VGND)
    );

    // With VPWR and VGND high, X follows A.
    check_output_follows_a_when_power_good: assert property (
        @($global_clock) (VPWR && VGND) |-> (X == A)
    );

    // A low forces X low.
    check_output_low_when_a_low: assert property (
        @($global_clock) !A |-> !X
    );

    // VPWR low forces X low.
    check_output_low_when_vpwr_low: assert property (
        @($global_clock) !VPWR |-> !X
    );

    // VGND low forces X low.
    check_output_low_when_vgnd_low: assert property (
        @($global_clock) !VGND |-> !X
    );

    // X high requires all three functional inputs high.
    check_output_high_requires_all_inputs: assert property (
        @($global_clock) X |-> (A && VPWR && VGND)
    );

endmodule