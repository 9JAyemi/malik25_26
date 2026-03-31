module nor4b_sva (
    input logic Y,
    input logic A,
    input logic B,
    input logic C,
    input logic D_N,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // Y must equal the NOR of all four data inputs.
    check_y_matches_nor: assert property (
        @($global_clock) Y == ~(A | B | C | D_N)
    );

    // All inputs low must drive Y high.
    check_all_inputs_low_drives_y_high: assert property (
        @($global_clock) (!A && !B && !C && !D_N) |-> Y
    );

    // Any high input must drive Y low.
    check_any_input_high_drives_y_low: assert property (
        @($global_clock) (A || B || C || D_N) |-> !Y
    );

    // Y high implies all inputs are low.
    check_y_high_implies_all_inputs_low: assert property (
        @($global_clock) Y |-> (!A && !B && !C && !D_N)
    );

    // Y low implies at least one input is high.
    check_y_low_implies_any_input_high: assert property (
        @($global_clock) !Y |-> (A || B || C || D_N)
    );

    // With stable data inputs, Y must remain stable.
    check_stable_y_when_inputs_stable: assert property (
        @($global_clock) $stable({A, B, C, D_N}) |-> $stable(Y)
    );

    // VPWR changes alone must not affect Y.
    check_vpwr_change_does_not_affect_y: assert property (
        @($global_clock) $stable({A, B, C, D_N}) && $changed(VPWR) |-> $stable(Y)
    );

    // VGND changes alone must not affect Y.
    check_vgnd_change_does_not_affect_y: assert property (
        @($global_clock) $stable({A, B, C, D_N}) && $changed(VGND) |-> $stable(Y)
    );

    // VPB changes alone must not affect Y.
    check_vpb_change_does_not_affect_y: assert property (
        @($global_clock) $stable({A, B, C, D_N}) && $changed(VPB) |-> $stable(Y)
    );

    // VNB changes alone must not affect Y.
    check_vnb_change_does_not_affect_y: assert property (
        @($global_clock) $stable({A, B, C, D_N}) && $changed(VNB) |-> $stable(Y)
    );

endmodule