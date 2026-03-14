module mux_sva #(
    parameter [7:0] INIT_VAL = 8'hB8
) (
    input logic ctrl,
    input logic D0,
    input logic D1,
    input logic S,
    input logic mux_out
);

    // S equals selected input on any input/control edge.
    check_mux_output_function: assert property (
        @(posedge ctrl or negedge ctrl or posedge D0 or negedge D0 or posedge D1 or negedge D1)
            S == (ctrl ? D1 : D0)
    );

    // On ctrl rising edge, S follows D1.
    check_ctrl_rise_select_D1: assert property (
        @(posedge ctrl) S == D1
    );

    // On ctrl falling edge, S follows D0.
    check_ctrl_fall_select_D0: assert property (
        @(negedge ctrl) S == D0
    );

    // When ctrl=1, S equals D1 at D1 edges.
    check_D1_edges_when_selected: assert property (
        @(posedge D1 or negedge D1) (ctrl == 1'b1) |-> (S == D1)
    );

    // When ctrl=0, S equals D0 at D0 edges.
    check_D0_edges_when_selected: assert property (
        @(posedge D0 or negedge D0) (ctrl == 1'b0) |-> (S == D0)
    );

    // When ctrl=0, D1 edges leave S equal to D0.
    check_unselected_D1_no_effect: assert property (
        @(posedge D1 or negedge D1) (ctrl == 1'b0) |-> (S == D0)
    );

    // When ctrl=1, D0 edges leave S equal to D1.
    check_unselected_D0_no_effect: assert property (
        @(posedge D0 or negedge D0) (ctrl == 1'b1) |-> (S == D1)
    );

    // S changes only if ctrl or the currently selected input changes.
    check_output_changes_only_on_ctrl_or_selected_input: assert property (
        @(posedge ctrl or negedge ctrl or posedge D0 or negedge D0 or posedge D1 or negedge D1)
            $changed(S) |-> ($changed(ctrl) || (ctrl && $changed(D1)) || (!ctrl && $changed(D0)))
    );

    // Internal mux_out reflects INIT_VAL bit indexed by ctrl on any edge.
    check_verilog_xl_mux_out_mapping: assert property (
        @(posedge ctrl or negedge ctrl or posedge D0 or negedge D0 or posedge D1 or negedge D1)
            mux_out == (ctrl ? INIT_VAL[0] : INIT_VAL[4])
    );

endmodule