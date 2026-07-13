module mux4to1_sva(
    input logic        clk,
    input logic [3:0]  in0,
    input logic [3:0]  in1,
    input logic [3:0]  in2,
    input logic [3:0]  in3,
    input logic [1:0]  sel,
    input logic [3:0]  out
);

    // sel=00 routes in0 to out.
    check_sel_00_routes_in0: assert property (
        @(posedge clk) disable iff (1'b0)
        (sel == 2'b00) |-> (out == in0)
    );

    // sel=01 routes in1 to out.
    check_sel_01_routes_in1: assert property (
        @(posedge clk) disable iff (1'b0)
        (sel == 2'b01) |-> (out == in1)
    );

    // sel=10 routes in2 to out.
    check_sel_10_routes_in2: assert property (
        @(posedge clk) disable iff (1'b0)
        (sel == 2'b10) |-> (out == in2)
    );

    // sel=11 routes in3 to out.
    check_sel_11_routes_in3: assert property (
        @(posedge clk) disable iff (1'b0)
        (sel == 2'b11) |-> (out == in3)
    );

endmodule