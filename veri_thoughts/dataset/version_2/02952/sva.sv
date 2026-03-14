module mux_2to1_enable_sva (
    input logic data_in_0,
    input logic data_in_1,
    input logic enable,
    input logic data_out
);
    // Output equals data_in_0 when enable is 0.
    check_select0_function: assert property (
        @(posedge enable or posedge data_in_0 or posedge data_in_1 or posedge data_out)
        (enable == 1'b0) |-> (data_out == data_in_0)
    );

    // Output equals data_in_1 when enable is 1.
    check_select1_function: assert property (
        @(posedge enable or posedge data_in_0 or posedge data_in_1 or posedge data_out)
        (enable == 1'b1) |-> (data_out == data_in_1)
    );

    // On enable rising edge, output selects data_in_1.
    check_out_on_enable_rise: assert property (
        @(posedge enable) data_out == data_in_1
    );

    // When enable=0, changes on data_in_1 alone do not change output.
    check_unselected_in1_no_effect: assert property (
        @(posedge data_in_1)
        (enable == 1'b0 && !$changed(enable) && $stable(data_in_0)) |-> $stable(data_out)
    );

    // When enable=1, changes on data_in_0 alone do not change output.
    check_unselected_in0_no_effect: assert property (
        @(posedge data_in_0)
        (enable == 1'b1 && !$changed(enable) && $stable(data_in_1)) |-> $stable(data_out)
    );

    // If both inputs are equal, output must match that value.
    check_equal_inputs_pass_through: assert property (
        @(posedge enable or posedge data_in_0 or posedge data_in_1 or posedge data_out)
        (data_in_0 == data_in_1) |-> (data_out == data_in_0)
    );
endmodule