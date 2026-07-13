module data_select_sva (
    input logic [15:0] x_axis,
    input logic [15:0] y_axis,
    input logic [15:0] z_axis,
    input logic [7:0]  temp_data,
    input logic [15:0] data,
    input logic [1:0]  sel
);

    // sel=00 routes x_axis to data.
    check_sel_00_routes_x_axis: assert property (
        @($global_clock) (sel === 2'b00) |-> (data === x_axis)
    );

    // sel=01 routes y_axis to data.
    check_sel_01_routes_y_axis: assert property (
        @($global_clock) (sel === 2'b01) |-> (data === y_axis)
    );

    // sel=10 routes z_axis to data.
    check_sel_10_routes_z_axis: assert property (
        @($global_clock) (sel === 2'b10) |-> (data === z_axis)
    );

    // sel=11 routes zero-extended temp_data to data.
    check_sel_11_routes_zero_extended_temp: assert property (
        @($global_clock) (sel === 2'b11) |-> (data === {8'h00, temp_data})
    );

    // data always matches the selected input or zero-extended temp_data.
    check_data_matches_selected_input: assert property (
        @($global_clock)
        1'b1 |-> (
            ((sel === 2'b00) && (data === x_axis)) ||
            ((sel === 2'b01) && (data === y_axis)) ||
            ((sel === 2'b10) && (data === z_axis)) ||
            ((sel === 2'b11) && (data === {8'h00, temp_data}))
        )
    );

endmodule