module Multiplexer_sva (
    input logic CLK,          // External sampling clock for assertions
    input logic ctrl,
    input logic [0:0] D0,
    input logic [0:0] D1,
    input logic [0:0] S
);
    // When ctrl is 0, S equals D0.
    check_select0: assert property (
        @(posedge CLK) (ctrl === 1'b0) |-> (S === D0)
    );

    // When ctrl is 1, S equals D1.
    check_select1: assert property (
        @(posedge CLK) (ctrl === 1'b1) |-> (S === D1)
    );

    // On ctrl rising edge, output selects D1.
    check_ctrl_rise_selects_D1: assert property (
        @(posedge CLK) $rose(ctrl) |-> (S === D1)
    );

    // On ctrl falling edge, output selects D0.
    check_ctrl_fall_selects_D0: assert property (
        @(posedge CLK) $fell(ctrl) |-> (S === D0)
    );

    // If all inputs are stable, S remains stable.
    check_stable_out_when_all_stable: assert property (
        @(posedge CLK) $stable(ctrl) && $stable(D0) && $stable(D1) |-> $stable(S)
    );

    // Changes on unselected input D1 do not affect S when ctrl=0.
    check_irrelevant_input_sel0_no_effect: assert property (
        @(posedge CLK) (ctrl === 1'b0) && $stable(ctrl) && $stable(D0) && $changed(D1) |-> $stable(S)
    );

    // Changes on unselected input D0 do not affect S when ctrl=1.
    check_irrelevant_input_sel1_no_effect: assert property (
        @(posedge CLK) (ctrl === 1'b1) && $stable(ctrl) && $stable(D1) && $changed(D0) |-> $stable(S)
    );

    // When ctrl=0 and D0 changes, S immediately reflects D0.
    check_selected_input_update_sel0: assert property (
        @(posedge CLK) (ctrl === 1'b0) && $stable(ctrl) && $changed(D0) |-> (S === D0)
    );

    // When ctrl=1 and D1 changes, S immediately reflects D1.
    check_selected_input_update_sel1: assert property (
        @(posedge CLK) (ctrl === 1'b1) && $stable(ctrl) && $changed(D1) |-> (S === D1)
    );

    // With ctrl=0 and differing inputs, S is not equal to D1.
    check_exclusive_if_inputs_differ_sel0: assert property (
        @(posedge CLK) (ctrl === 1'b0) && (D0 !== D1) |-> (S !== D1)
    );

    // With ctrl=1 and differing inputs, S is not equal to D0.
    check_exclusive_if_inputs_differ_sel1: assert property (
        @(posedge CLK) (ctrl === 1'b1) && (D0 !== D1) |-> (S !== D0)
    );
endmodule