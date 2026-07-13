module data_select_sva (
    input logic        clk,
    input logic [15:0] x_axis,
    input logic [15:0] y_axis,
    input logic [15:0] z_axis,
    input logic [7:0]  temp_data,
    input logic [1:0]  sel,
    input logic [15:0] data
);

    // When sel selects x_axis, data must match x_axis.
    check_select_x_axis: assert property (
        @(posedge clk) disable iff (1'b0)
        (sel == 2'b00) |-> (data == x_axis)
    );

    // When sel selects y_axis, data must match y_axis.
    check_select_y_axis: assert property (
        @(posedge clk) disable iff (1'b0)
        (sel == 2'b01) |-> (data == y_axis)
    );

    // When sel selects z_axis, data must match z_axis.
    check_select_z_axis: assert property (
        @(posedge clk) disable iff (1'b0)
        (sel == 2'b10) |-> (data == z_axis)
    );

    // When sel selects temp_data, data must be zero-extended temp_data.
    check_select_temp_data: assert property (
        @(posedge clk) disable iff (1'b0)
        (sel == 2'b11) |-> (data == {8'h00, temp_data})
    );

    // With x_axis selected and unchanged, data must remain unchanged.
    check_x_axis_stability: assert property (
        @(posedge clk) disable iff (1'b0)
        ($stable(sel) && (sel == 2'b00) && $stable(x_axis)) |-> $stable(data)
    );

    // With y_axis selected and unchanged, data must remain unchanged.
    check_y_axis_stability: assert property (
        @(posedge clk) disable iff (1'b0)
        ($stable(sel) && (sel == 2'b01) && $stable(y_axis)) |-> $stable(data)
    );

    // With z_axis selected and unchanged, data must remain unchanged.
    check_z_axis_stability: assert property (
        @(posedge clk) disable iff (1'b0)
        ($stable(sel) && (sel == 2'b10) && $stable(z_axis)) |-> $stable(data)
    );

    // With temp_data selected and unchanged, data must remain unchanged.
    check_temp_data_stability: assert property (
        @(posedge clk) disable iff (1'b0)
        ($stable(sel) && (sel == 2'b11) && $stable(temp_data)) |-> $stable(data)
    );

endmodule