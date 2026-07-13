module mux4to1_sva(
    input logic clk,
    input logic [7:0] data_in0,
    input logic [7:0] data_in1,
    input logic [7:0] data_in2,
    input logic [7:0] data_in3,
    input logic sel0,
    input logic sel1,
    input logic [7:0] data_out
);

    // When sel is 00, data_out must equal data_in0.
    check_sel_00_routes_input0: assert property (
        @(posedge clk) ({sel1, sel0} == 2'b00) |-> (data_out == data_in0)
    );

    // When sel is 01, data_out must equal data_in1.
    check_sel_01_routes_input1: assert property (
        @(posedge clk) ({sel1, sel0} == 2'b01) |-> (data_out == data_in1)
    );

    // When sel is 10, data_out must equal data_in2.
    check_sel_10_routes_input2: assert property (
        @(posedge clk) ({sel1, sel0} == 2'b10) |-> (data_out == data_in2)
    );

    // When sel is 11, data_out must equal data_in3.
    check_sel_11_routes_input3: assert property (
        @(posedge clk) ({sel1, sel0} == 2'b11) |-> (data_out == data_in3)
    );

endmodule