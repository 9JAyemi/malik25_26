module data_select_sva (
    input logic clk,
    input logic rst_n,
    input logic [15:0] x_axis,
    input logic [15:0] y_axis,
    input logic [15:0] z_axis,
    input logic [7:0] temp_data,
    input logic [1:0] sel,
    output logic [15:0] data
);
    // Sequential logic driven by sel, x_axis, y_axis, z_axis, temp_data
    // Data is selected based on the value of sel
    // At reset, data should be 0

    // Data should be x_axis when sel is 00
    sel_00: assert property (
        @(posedge clk) disable iff (!rst_n) (sel == 2'b00) |-> (data == x_axis)
    );

    // Data should be y_axis when sel is 01
    sel_01: assert property (
        @(posedge clk) disable iff (!rst_n) (sel == 2'b01) |-> (data == y_axis)
    );

    // Data should be z_axis when sel is 10
    sel_10: assert property (
        @(posedge clk) disable iff (!rst_n) (sel == 2'b10) |-> (data == z_axis)
    );

    // Data should be {8'h00, temp_data} when sel is 11
    sel_11: assert property (
        @(posedge clk) disable iff (!rst_n) (sel == 2'b11) |-> (data == {8'h00, temp_data})
    );

    // At reset, data should be 0
    reset: assert property (
        @(posedge clk) !rst_n |-> (data == 16'h0000)
    );

endmodule