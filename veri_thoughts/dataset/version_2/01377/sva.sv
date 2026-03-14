module mux_sva #(
    parameter WIDTH = 1
)(
    input logic clk,
    input logic ctrl,
    input logic [WIDTH-1:0] D0,
    input logic [WIDTH-1:0] D1,
    input logic [WIDTH-1:0] S
);

    // Output equals the selected input each cycle.
    check_mux_function_correctness: assert property (
        @(posedge clk) S == (ctrl ? D1 : D0)
    );

    // On ctrl rising edge, output reflects D1 in the same cycle.
    check_select_to_output_on_ctrl_rise: assert property (
        @(posedge clk) $rose(ctrl) |-> (S == D1)
    );

    // On ctrl falling edge, output reflects D0 in the same cycle.
    check_select_to_output_on_ctrl_fall: assert property (
        @(posedge clk) $fell(ctrl) |-> (S == D0)
    );

    // When selecting D0, changes on D1 do not affect S.
    check_unselected_input_ignored_when_ctrl0: assert property (
        @(posedge clk) (ctrl == 1'b0) && $changed(D1) |-> (S == D0)
    );

    // When selecting D1, changes on D0 do not affect S.
    check_unselected_input_ignored_when_ctrl1: assert property (
        @(posedge clk) (ctrl == 1'b1) && $changed(D0) |-> (S == D1)
    );

    // When selecting D0, S tracks D0 on any change.
    check_output_tracks_D0_when_selected: assert property (
        @(posedge clk) (ctrl == 1'b0) && $changed(D0) |-> (S == D0)
    );

    // When selecting D1, S tracks D1 on any change.
    check_output_tracks_D1_when_selected: assert property (
        @(posedge clk) (ctrl == 1'b1) && $changed(D1) |-> (S == D1)
    );

    // If ctrl, D0, and D1 are all stable, S remains stable.
    check_output_stable_when_inputs_and_ctrl_stable: assert property (
        @(posedge clk) $stable({ctrl, D0, D1}) |-> $stable(S)
    );

    // If ctrl selects D0 and D0 is stable, S remains stable (independent of D1).
    check_output_stable_when_ctrl0_and_D0_stable: assert property (
        @(posedge clk) (ctrl == 1'b0) && $stable(D0) |-> $stable(S)
    );

    // If ctrl selects D1 and D1 is stable, S remains stable (independent of D0).
    check_output_stable_when_ctrl1_and_D1_stable: assert property (
        @(posedge clk) (ctrl == 1'b1) && $stable(D1) |-> $stable(S)
    );

endmodule