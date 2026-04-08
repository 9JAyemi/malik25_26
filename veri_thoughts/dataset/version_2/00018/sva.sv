module mux_4to1_sva (
    input logic clk,
    input logic [3:0] in,
    input logic [1:0] sel,
    input logic out
);

    // When sel is 2'b00, out must reflect in[0].
    check_sel_00_routes_in0: assert property (
        @(posedge clk) (sel == 2'b00) |-> (out == in[0])
    );

    // When sel is 2'b01, out must reflect in[1].
    check_sel_01_routes_in1: assert property (
        @(posedge clk) (sel == 2'b01) |-> (out == in[1])
    );

    // When sel is 2'b10, out must reflect in[2].
    check_sel_10_routes_in2: assert property (
        @(posedge clk) (sel == 2'b10) |-> (out == in[2])
    );

    // When sel is 2'b11, out must reflect in[3].
    check_sel_11_routes_in3: assert property (
        @(posedge clk) (sel == 2'b11) |-> (out == in[3])
    );

endmodule