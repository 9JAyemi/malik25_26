module mux2to1_sva (
    input logic data_in_0,
    input logic data_in_1,
    input logic ctrl,
    input logic data_out
);

    // When ctrl is low, the output must match data_in_0.
    check_select_low_routes_input0: assert property (
        @($global_clock) disable iff (1'b0)
        (ctrl == 1'b0) |-> (data_out == data_in_0)
    );

    // When ctrl is high, the output must match data_in_1.
    check_select_high_routes_input1: assert property (
        @($global_clock) disable iff (1'b0)
        (ctrl == 1'b1) |-> (data_out == data_in_1)
    );

    // With ctrl low and data_in_0 stable, the output must stay stable.
    check_output_stable_when_input0_selected: assert property (
        @($global_clock) disable iff (1'b0)
        ($stable(ctrl) && (ctrl == 1'b0) && $stable(data_in_0)) |-> $stable(data_out)
    );

    // With ctrl high and data_in_1 stable, the output must stay stable.
    check_output_stable_when_input1_selected: assert property (
        @($global_clock) disable iff (1'b0)
        ($stable(ctrl) && (ctrl == 1'b1) && $stable(data_in_1)) |-> $stable(data_out)
    );

    // A change on data_in_0 must update the output when ctrl stays low.
    check_input0_change_propagates_when_selected: assert property (
        @($global_clock) disable iff (1'b0)
        ($stable(ctrl) && (ctrl == 1'b0) && $changed(data_in_0)) |-> ($changed(data_out) && (data_out == data_in_0))
    );

    // A change on data_in_1 must update the output when ctrl stays high.
    check_input1_change_propagates_when_selected: assert property (
        @($global_clock) disable iff (1'b0)
        ($stable(ctrl) && (ctrl == 1'b1) && $changed(data_in_1)) |-> ($changed(data_out) && (data_out == data_in_1))
    );

    // A rising ctrl must switch the output to data_in_1.
    check_ctrl_rise_selects_input1: assert property (
        @($global_clock) disable iff (1'b0)
        $rose(ctrl) |-> (data_out == data_in_1)
    );

    // A falling ctrl must switch the output to data_in_0.
    check_ctrl_fall_selects_input0: assert property (
        @($global_clock) disable iff (1'b0)
        $fell(ctrl) |-> (data_out == data_in_0)
    );

    // If both inputs are equal, the output must equal that common value.
    check_equal_inputs_force_common_output: assert property (
        @($global_clock) disable iff (1'b0)
        (data_in_0 == data_in_1) |-> (data_out == data_in_0)
    );

endmodule