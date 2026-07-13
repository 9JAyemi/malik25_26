module mux_4to1_using_2to1_sva (
    input logic clk,
    input logic [7:0] data0,
    input logic [7:0] data1,
    input logic [7:0] data2,
    input logic [7:0] data3,
    input logic [1:0] sel,
    input logic [7:0] out
);

    // Output matches the implemented nested mux expression.
    check_output_matches_mux_tree: assert property (
        @(posedge clk)
        out == (sel[1] ? (sel[0] ? data3 : data2) : (sel[0] ? data1 : data0))
    );

    // sel=00 routes data0 to the output.
    check_sel_00_routes_data0: assert property (
        @(posedge clk)
        (sel == 2'b00) |-> (out == data0)
    );

    // sel=01 routes data1 to the output.
    check_sel_01_routes_data1: assert property (
        @(posedge clk)
        (sel == 2'b01) |-> (out == data1)
    );

    // sel=10 routes data2 to the output.
    check_sel_10_routes_data2: assert property (
        @(posedge clk)
        (sel == 2'b10) |-> (out == data2)
    );

    // sel=11 routes data3 to the output.
    check_sel_11_routes_data3: assert property (
        @(posedge clk)
        (sel == 2'b11) |-> (out == data3)
    );

endmodule