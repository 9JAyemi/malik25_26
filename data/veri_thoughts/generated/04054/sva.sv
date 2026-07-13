module my_module_sva (
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // No RTL clock or reset is present; sample on the global formal clock.

    // X must match the implemented combinational logic.
    check_x_matches_logic: assert property (
        @($global_clock)
        X == (((A2 | A1) & (B2 | B1)) & VPWR & ~VGND)
    );

    // Ground asserted forces X low.
    check_vgnd_forces_x_low: assert property (
        @($global_clock)
        VGND |-> !X
    );

    // Power removed forces X low.
    check_vpwr_required_for_x: assert property (
        @($global_clock)
        !VPWR |-> !X
    );

    // If both A inputs are low, X must be low.
    check_a_or_required: assert property (
        @($global_clock)
        !(A2 | A1) |-> !X
    );

    // If both B inputs are low, X must be low.
    check_b_or_required: assert property (
        @($global_clock)
        !(B2 | B1) |-> !X
    );

    // When both input OR terms are high and power is good, X must be high.
    check_all_conditions_drive_x_high: assert property (
        @($global_clock)
        ((A2 | A1) & (B2 | B1) & VPWR & ~VGND) |-> X
    );

    // A high X requires both input OR terms and good power conditions.
    check_x_high_requires_valid_conditions: assert property (
        @($global_clock)
        X |-> ((A2 | A1) & (B2 | B1) & VPWR & ~VGND)
    );

endmodule