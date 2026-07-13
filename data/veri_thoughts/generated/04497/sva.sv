module mux4to1_sva (
    input logic       clk,
    input logic [3:0] data_in,
    input logic [1:0] sel,
    input logic       data_out,
    input logic       data_out_temp0,
    input logic       data_out_temp1
);

    // Combinational RTL with no native reset; sample on an external clock.

    // Lower 2:1 mux routes data_in[0] when sel[0] is low.
    check_temp0_selects_data0: assert property (
        @(posedge clk) (sel[0] == 1'b0) |-> (data_out_temp0 == data_in[0])
    );

    // Lower 2:1 mux routes data_in[1] when sel[0] is high.
    check_temp0_selects_data1: assert property (
        @(posedge clk) (sel[0] == 1'b1) |-> (data_out_temp0 == data_in[1])
    );

    // Upper 2:1 mux routes data_in[2] when sel[0] is low.
    check_temp1_selects_data2: assert property (
        @(posedge clk) (sel[0] == 1'b0) |-> (data_out_temp1 == data_in[2])
    );

    // Upper 2:1 mux routes data_in[3] when sel[0] is high.
    check_temp1_selects_data3: assert property (
        @(posedge clk) (sel[0] == 1'b1) |-> (data_out_temp1 == data_in[3])
    );

    // Final 2:1 mux routes data_out_temp0 when sel[1] is low.
    check_output_selects_temp0: assert property (
        @(posedge clk) (sel[1] == 1'b0) |-> (data_out == data_out_temp0)
    );

    // Final 2:1 mux routes data_out_temp1 when sel[1] is high.
    check_output_selects_temp1: assert property (
        @(posedge clk) (sel[1] == 1'b1) |-> (data_out == data_out_temp1)
    );

    // Top-level mux routes data_in[0] for select 2'b00.
    check_sel_00_routes_data0: assert property (
        @(posedge clk) (sel == 2'b00) |-> (data_out == data_in[0])
    );

    // Top-level mux routes data_in[1] for select 2'b01.
    check_sel_01_routes_data1: assert property (
        @(posedge clk) (sel == 2'b01) |-> (data_out == data_in[1])
    );

    // Top-level mux routes data_in[2] for select 2'b10.
    check_sel_10_routes_data2: assert property (
        @(posedge clk) (sel == 2'b10) |-> (data_out == data_in[2])
    );

    // Top-level mux routes data_in[3] for select 2'b11.
    check_sel_11_routes_data3: assert property (
        @(posedge clk) (sel == 2'b11) |-> (data_out == data_in[3])
    );

endmodule