module or4_2_custom_sva (
    input logic X,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // X must equal the OR of all four data inputs.
    check_x_matches_or4: assert property (
        @($global_clock) X == (A | B | C | D)
    );

    // If all inputs are low, X must be low.
    check_all_inputs_low_drives_x_low: assert property (
        @($global_clock) !(A | B | C | D) |-> !X
    );

    // If any input is high, X must be high.
    check_any_input_high_drives_x_high: assert property (
        @($global_clock) (A | B | C | D) |-> X
    );

    // X can only be high when at least one input is high.
    check_x_high_requires_some_input_high: assert property (
        @($global_clock) X |-> (A | B | C | D)
    );

    // X can only be low when all inputs are low.
    check_x_low_requires_all_inputs_low: assert property (
        @($global_clock) !X |-> !(A | B | C | D)
    );

    // With stable data inputs, X must remain stable.
    check_stable_data_inputs_keep_x_stable: assert property (
        @($global_clock) $stable({A, B, C, D}) |-> $stable(X)
    );

    // With stable data inputs, a change on X must be caused by a power pin change.
    check_x_change_requires_power_pin_change: assert property (
        @($global_clock) ($changed(X) && $stable({A, B, C, D})) |-> $changed({VPWR, VGND, VPB, VNB})
    );

    // With stable power pins, a change on X must be caused by a data input change.
    check_x_change_requires_data_pin_change: assert property (
        @($global_clock) ($changed(X) && $stable({VPWR, VGND, VPB, VNB})) |-> $changed({A, B, C, D})
    );

endmodule