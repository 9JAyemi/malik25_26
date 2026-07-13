module and_module_sva (
    input logic X,
    input logic A_N,
    input logic B_N,
    input logic C,
    input logic D,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // Combinational DUT with no explicit clock or reset; sample on the global formal clock.

    // X must equal the AND of the four functional inputs.
    check_x_equation: assert property (
        @($global_clock) X == (A_N & B_N & C & D)
    );

    // A high X requires all four functional inputs to be high.
    check_x_high_requires_all_inputs_high: assert property (
        @($global_clock) X |-> (A_N & B_N & C & D)
    );

    // All four functional inputs high must drive X high.
    check_all_inputs_high_drive_x: assert property (
        @($global_clock) (A_N & B_N & C & D) |-> X
    );

    // If any functional input is low, X must be low.
    check_any_low_input_forces_x_low: assert property (
        @($global_clock) !(A_N & B_N & C & D) |-> !X
    );

    // With stable functional inputs, X must remain stable.
    check_stable_function_inputs_keep_x_stable: assert property (
        @($global_clock) $stable({A_N, B_N, C, D}) |-> $stable(X)
    );

    // Power pin changes alone must not affect X.
    check_power_pin_changes_do_not_affect_x: assert property (
        @($global_clock) $stable({A_N, B_N, C, D}) && $changed({VPWR, VGND, VPB, VNB}) |-> $stable(X)
    );

endmodule