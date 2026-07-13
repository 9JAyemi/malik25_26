module Mux_3x1_b_sva #(
    parameter W = 32
) (
    input  logic                   clk,      // verification clock
    input  logic [1:0]             select,
    input  logic [W-1:0]           ch_0,
    input  logic [W-1:0]           ch_1,
    input  logic [W-1:0]           ch_2,
    input  logic [W-1:0]           data_out
);
    // When select is 2'b00, data_out must equal ch_0.
    check_sel00_routes_ch0: assert property (
        @(posedge clk) (select == 2'b00) |-> (data_out == ch_0)
    );

    // When select is 2'b01, data_out must equal ch_1.
    check_sel01_routes_ch1: assert property (
        @(posedge clk) (select == 2'b01) |-> (data_out == ch_1)
    );

    // When select is 2'b10, data_out must equal ch_2.
    check_sel10_routes_ch2: assert property (
        @(posedge clk) (select == 2'b10) |-> (data_out == ch_2)
    );

    // When select is 2'b11, data_out must be all zeros.
    check_sel11_routes_zero: assert property (
        @(posedge clk) (select == 2'b11) |-> (data_out == {W{1'b0}})
    );

    // Combined functional mapping summary for all select values.
    check_functional_mapping: assert property (
        @(posedge clk)
            ((select == 2'b00) && (data_out == ch_0)) ||
            ((select == 2'b01) && (data_out == ch_1)) ||
            ((select == 2'b10) && (data_out == ch_2)) ||
            ((select == 2'b11) && (data_out == {W{1'b0}}))
    );
endmodule