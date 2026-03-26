module mux4to1_sva (
    input logic        clk,
    input logic [3:0]  in0,
    input logic [3:0]  in1,
    input logic [3:0]  in2,
    input logic [3:0]  in3,
    input logic        sel0,
    input logic        sel1,
    input logic [3:0]  out
);

    // Output matches the implemented mux expression.
    check_mux_function: assert property (
        @(posedge clk)
        out == (({sel1, sel0} == 2'b00) ? in0 :
                ({sel1, sel0} == 2'b01) ? in1 :
                ({sel1, sel0} == 2'b10) ? in2 :
                in3)
    );

    // Select 00 routes in0 to out.
    check_sel_00_routes_in0: assert property (
        @(posedge clk)
        ({sel1, sel0} == 2'b00) |-> (out == in0)
    );

    // Select 01 routes in1 to out.
    check_sel_01_routes_in1: assert property (
        @(posedge clk)
        ({sel1, sel0} == 2'b01) |-> (out == in1)
    );

    // Select 10 routes in2 to out.
    check_sel_10_routes_in2: assert property (
        @(posedge clk)
        ({sel1, sel0} == 2'b10) |-> (out == in2)
    );

    // Select 11 routes in3 to out.
    check_sel_11_routes_in3: assert property (
        @(posedge clk)
        ({sel1, sel0} == 2'b11) |-> (out == in3)
    );

endmodule