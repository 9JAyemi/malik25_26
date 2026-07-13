module mux_2_to_1_sva (
    input logic clk,
    input logic select,
    input logic data_0,
    input logic data_1,
    input logic out
);
    // Mux function: out equals selected input.
    check_mux_equivalence: assert property (
        @(posedge clk) out == (select ? data_1 : data_0)
    );

    // When select=0, out equals data_0.
    check_select0_routes_data0: assert property (
        @(posedge clk) (select == 1'b0) |-> (out == data_0)
    );

    // When select=1, out equals data_1.
    check_select1_routes_data1: assert property (
        @(posedge clk) (select == 1'b1) |-> (out == data_1)
    );

    // If inputs are equal, out equals that value.
    check_equal_inputs_pass_through: assert property (
        @(posedge clk) (data_0 == data_1) |-> (out == data_0)
    );

    // Out is stable when select and data inputs are stable.
    check_stable_when_inputs_stable: assert property (
        @(posedge clk) ($stable(select) && $stable(data_0) && $stable(data_1)) |-> $stable(out)
    );

    // Out change implies at least one of select/data_0/data_1 changed.
    check_out_change_requires_input_change: assert property (
        @(posedge clk) $changed(out) |-> ($changed(select) || $changed(data_0) || $changed(data_1))
    );

    // If select=0 and data_0 changes (select stable), out follows and changes.
    check_data0_change_propagates_when_selected: assert property (
        @(posedge clk) (select == 1'b0 && $stable(select) && $changed(data_0)) |-> ($changed(out) && (out == data_0))
    );

    // If select=1 and data_1 changes (select stable), out follows and changes.
    check_data1_change_propagates_when_selected: assert property (
        @(posedge clk) (select == 1'b1 && $stable(select) && $changed(data_1)) |-> ($changed(out) && (out == data_1))
    );

    // If select=1 and data_0 changes (select stable), out stays stable.
    check_unselected_data0_no_effect: assert property (
        @(posedge clk) (select == 1'b1 && $stable(select) && $changed(data_0)) |-> $stable(out)
    );

    // If select=0 and data_1 changes (select stable), out stays stable.
    check_unselected_data1_no_effect: assert property (
        @(posedge clk) (select == 1'b0 && $stable(select) && $changed(data_1)) |-> $stable(out)
    );

    // On select rising edge with stable data, out switches from data_0 to data_1.
    check_out_updates_on_select_rise: assert property (
        @(posedge clk) ($rose(select) && $stable(data_0) && $stable(data_1)) |-> ($past(out) == $past(data_0) && out == data_1)
    );

    // On select falling edge with stable data, out switches from data_1 to data_0.
    check_out_updates_on_select_fall: assert property (
        @(posedge clk) ($fell(select) && $stable(data_0) && $stable(data_1)) |-> ($past(out) == $past(data_1) && out == data_0)
    );
endmodule