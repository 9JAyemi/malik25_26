module data_select_sva (
    input logic        clk,
    input logic [15:0] x_axis,
    input logic [15:0] y_axis,
    input logic [15:0] z_axis,
    input logic [7:0]  temp_data,
    input logic [15:0] data,
    input logic [1:0]  sel
);

// sel=00 routes x_axis to data.
    check_sel_x_axis: assert property (
        @(posedge clk) (sel == 2'b00) |-> (data == x_axis)
    );

// sel=01 routes y_axis to data.
    check_sel_y_axis: assert property (
        @(posedge clk) (sel == 2'b01) |-> (data == y_axis)
    );

// sel=10 routes z_axis to data.
    check_sel_z_axis: assert property (
        @(posedge clk) (sel == 2'b10) |-> (data == z_axis)
    );

// sel=11 routes temp_data into the upper byte of data.
    check_sel_temp_data: assert property (
        @(posedge clk) (sel == 2'b11) |-> (data == {8'h00, temp_data})
    );

// data always matches the selected input or zero-extended temp_data.
    check_output_matches_select: assert property (
        @(posedge clk)
            (data == (sel == 2'b00 ? x_axis :
                      sel == 2'b01 ? y_axis :
                      sel == 2'b10 ? z_axis :
                                     {8'h00, temp_data}))
    );

endmodule
