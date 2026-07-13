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
    check_sel_00_routes_x_axis: assert property (
        @(posedge clk) (sel == 2'b00) |-> (data == x_axis)
    );

    // sel=01 routes y_axis to data.
    check_sel_01_routes_y_axis: assert property (
        @(posedge clk) (sel == 2'b01) |-> (data == y_axis)
    );

    // sel=10 routes z_axis to data.
    check_sel_10_routes_z_axis: assert property (
        @(posedge clk) (sel == 2'b10) |-> (data == z_axis)
    );

    // sel=11 routes zero-extended temp_data to data.
    check_sel_11_routes_zero_extended_temp: assert property (
        @(posedge clk) (sel == 2'b11) |-> (data == {8'h00, temp_data})
    );

    // With sel=00 held and x_axis stable, data remains stable.
    check_sel_00_stable_when_x_stable: assert property (
        @(posedge clk) (sel == 2'b00 && $stable(sel) && $stable(x_axis)) |-> $stable(data)
    );

    // With sel=01 held and y_axis stable, data remains stable.
    check_sel_01_stable_when_y_stable: assert property (
        @(posedge clk) (sel == 2'b01 && $stable(sel) && $stable(y_axis)) |-> $stable(data)
    );

    // With sel=10 held and z_axis stable, data remains stable.
    check_sel_10_stable_when_z_stable: assert property (
        @(posedge clk) (sel == 2'b10 && $stable(sel) && $stable(z_axis)) |-> $stable(data)
    );

    // With sel=11 held and temp_data stable, data remains stable.
    check_sel_11_stable_when_temp_stable: assert property (
        @(posedge clk) (sel == 2'b11 && $stable(sel) && $stable(temp_data)) |-> $stable(data)
    );

    // With sel=00 held and x_axis changing, data changes accordingly.
    check_sel_00_tracks_x_axis: assert property (
        @(posedge clk) (sel == 2'b00 && $stable(sel) && $changed(x_axis)) |-> $changed(data)
    );

    // With sel=01 held and y_axis changing, data changes accordingly.
    check_sel_01_tracks_y_axis: assert property (
        @(posedge clk) (sel == 2'b01 && $stable(sel) && $changed(y_axis)) |-> $changed(data)
    );

    // With sel=10 held and z_axis changing, data changes accordingly.
    check_sel_10_tracks_z_axis: assert property (
        @(posedge clk) (sel == 2'b10 && $stable(sel) && $changed(z_axis)) |-> $changed(data)
    );

    // With sel=11 held and temp_data changing, data changes accordingly.
    check_sel_11_tracks_temp_data: assert property (
        @(posedge clk) (sel == 2'b11 && $stable(sel) && $changed(temp_data)) |-> $changed(data)
    );

endmodule