module mux_sva (
    input logic clk,
    input logic ctrl,
    input logic [0:0] D0,
    input logic [0:0] D1,
    input logic [0:0] S
);
    // Output equals the mux expression.
    check_mux_equation: assert property (
        @(posedge clk) S == ((ctrl == 1'b0) ? D0 : D1)
    );

    // When ctrl is 0, S must equal D0.
    check_ctrl_low_selects_D0: assert property (
        @(posedge clk) (ctrl == 1'b0) |-> (S == D0)
    );

    // When ctrl is 1, S must equal D1.
    check_ctrl_high_selects_D1: assert property (
        @(posedge clk) (ctrl == 1'b1) |-> (S == D1)
    );

    // On rising ctrl edge, S must reflect D1.
    check_output_updates_on_ctrl_rise: assert property (
        @(posedge clk) $rose(ctrl) |-> (S == D1)
    );

    // On falling ctrl edge, S must reflect D0.
    check_output_updates_on_ctrl_fall: assert property (
        @(posedge clk) $fell(ctrl) |-> (S == D0)
    );

    // If ctrl, D0, and D1 are stable, S must be stable.
    check_output_stable_if_inputs_stable: assert property (
        @(posedge clk) $stable(ctrl) && $stable(D0) && $stable(D1) |-> $stable(S)
    );

    // With ctrl stable at 0, changes on D1 must not affect S.
    check_ignore_unselected_D1: assert property (
        @(posedge clk) $stable(ctrl) && (ctrl == 1'b0) && $changed(D1) |-> $stable(S)
    );

    // With ctrl stable at 1, changes on D0 must not affect S.
    check_ignore_unselected_D0: assert property (
        @(posedge clk) $stable(ctrl) && (ctrl == 1'b1) && $changed(D0) |-> $stable(S)
    );

    // With ctrl stable at 0, changes on D0 must propagate to S.
    check_selected_input_propagates_low: assert property (
        @(posedge clk) $stable(ctrl) && (ctrl == 1'b0) && $changed(D0) |-> $changed(S)
    );

    // With ctrl stable at 1, changes on D1 must propagate to S.
    check_selected_input_propagates_high: assert property (
        @(posedge clk) $stable(ctrl) && (ctrl == 1'b1) && $changed(D1) |-> $changed(S)
    );
endmodule