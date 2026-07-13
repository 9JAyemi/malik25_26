module mux4to1_sva(
    input logic [3:0] in,
    input logic [1:0] sel,
    input logic       out,
    input logic       clk
);

    // Select 00 routes in[0] to out.
    check_sel_00_routes_in0: assert property (
        @(posedge clk) (sel == 2'b00) |-> (out == in[0])
    );

    // Select 01 routes in[1] to out.
    check_sel_01_routes_in1: assert property (
        @(posedge clk) (sel == 2'b01) |-> (out == in[1])
    );

    // Select 10 routes in[2] to out.
    check_sel_10_routes_in2: assert property (
        @(posedge clk) (sel == 2'b10) |-> (out == in[2])
    );

    // Select 11 routes in[3] to out.
    check_sel_11_routes_in3: assert property (
        @(posedge clk) (sel == 2'b11) |-> (out == in[3])
    );

endmodule