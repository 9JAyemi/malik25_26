module mux4to1_sva (
    input logic clk,
    input logic in0,
    input logic in1,
    input logic in2,
    input logic in3,
    input logic [1:0] sel,
    input logic out
);

    // Overall output matches the implemented 4:1 mux equation.
    check_mux_equation: assert property (
        @(posedge clk)
        out == (sel[1] ? (sel[0] ? in3 : in2) : (sel[0] ? in1 : in0))
    );

    // sel=00 routes in0 to out.
    check_sel00_routes_in0: assert property (
        @(posedge clk)
        (sel == 2'b00) |-> (out == in0)
    );

    // sel=01 routes in1 to out.
    check_sel01_routes_in1: assert property (
        @(posedge clk)
        (sel == 2'b01) |-> (out == in1)
    );

    // sel=10 routes in2 to out.
    check_sel10_routes_in2: assert property (
        @(posedge clk)
        (sel == 2'b10) |-> (out == in2)
    );

    // sel=11 routes in3 to out.
    check_sel11_routes_in3: assert property (
        @(posedge clk)
        (sel == 2'b11) |-> (out == in3)
    );

    // sel[1]=0 selects between the lower input pair.
    check_lower_pair_selection: assert property (
        @(posedge clk)
        (sel[1] == 1'b0) |-> (out == (sel[0] ? in1 : in0))
    );

    // sel[1]=1 selects between the upper input pair.
    check_upper_pair_selection: assert property (
        @(posedge clk)
        (sel[1] == 1'b1) |-> (out == (sel[0] ? in3 : in2))
    );

endmodule