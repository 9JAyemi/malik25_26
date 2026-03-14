module mux_1bit_sva (
    input logic CLK,
    input logic ctrl,
    input logic [0:0] D0,
    input logic [0:0] D1,
    input logic [0:0] S
);

    // S equals the selected data input (functional equivalence).
    check_mux_functional_equivalence: assert property (
        @(posedge CLK) S == (ctrl ? D1 : D0)
    );

    // When ctrl is 0, S equals D0.
    check_select_D0_when_ctrl_0: assert property (
        @(posedge CLK) (ctrl == 1'b0) |-> (S == D0)
    );

    // When ctrl is 1, S equals D1.
    check_select_D1_when_ctrl_1: assert property (
        @(posedge CLK) (ctrl == 1'b1) |-> (S == D1)
    );

    // On ctrl rising edge, S reflects D1.
    check_output_on_ctrl_rise_selects_D1: assert property (
        @(posedge CLK) $rose(ctrl) |-> (S == D1)
    );

    // On ctrl falling edge, S reflects D0.
    check_output_on_ctrl_fall_selects_D0: assert property (
        @(posedge CLK) $fell(ctrl) |-> (S == D0)
    );

    // With ctrl=0, changes on D1 do not affect S if ctrl and D0 are stable.
    check_unselected_input_no_effect_when_ctrl_0: assert property (
        @(posedge CLK) (ctrl == 1'b0) && $stable(ctrl) && $stable(D0) && $changed(D1) |-> $stable(S)
    );

    // With ctrl=1, changes on D0 do not affect S if ctrl and D1 are stable.
    check_unselected_input_no_effect_when_ctrl_1: assert property (
        @(posedge CLK) (ctrl == 1'b1) && $stable(ctrl) && $stable(D1) && $changed(D0) |-> $stable(S)
    );

    // If ctrl, D0, and D1 are stable, S remains stable (pure combinational).
    check_output_stable_when_all_inputs_stable: assert property (
        @(posedge CLK) $stable(ctrl) && $stable(D0) && $stable(D1) |-> $stable(S)
    );

    // With ctrl=0 and stable, S changes iff D0 changes.
    check_output_tracks_D0_when_ctrl_0_changes: assert property (
        @(posedge CLK) (ctrl == 1'b0) && $stable(ctrl) && $changed(D0) |-> $changed(S)
    );

    // With ctrl=1 and stable, S changes iff D1 changes.
    check_output_tracks_D1_when_ctrl_1_changes: assert property (
        @(posedge CLK) (ctrl == 1'b1) && $stable(ctrl) && $changed(D1) |-> $changed(S)
    );

    // If ctrl toggles and the newly selected input differs from the previously selected input, S changes.
    check_sel_toggle_changes_output_if_new_selected_differs_from_prev_selected: assert property (
        @(posedge CLK)
            $changed(ctrl) && (
                (ctrl && (D1 != $past(D0))) ||
                (!ctrl && (D0 != $past(D1)))
            ) |-> $changed(S)
    );

    // If D0 equals D1, S equals that value regardless of ctrl.
    check_equal_inputs_force_S_equal: assert property (
        @(posedge CLK) (D0 == D1) |-> (S == D0)
    );

endmodule