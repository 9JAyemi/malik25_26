module mux4to1_sva (
    input logic out,
    input logic in0,
    input logic in1,
    input logic in2,
    input logic in3,
    input logic sel0,
    input logic sel1
);

    // Select 00 routes in0 to out.
    check_sel_00_routes_in0: assert property (
        @($global_clock) ({sel1, sel0} == 2'b00) |-> (out == in0)
    );

    // Select 01 routes in1 to out.
    check_sel_01_routes_in1: assert property (
        @($global_clock) ({sel1, sel0} == 2'b01) |-> (out == in1)
    );

    // Select 10 routes in2 to out.
    check_sel_10_routes_in2: assert property (
        @($global_clock) ({sel1, sel0} == 2'b10) |-> (out == in2)
    );

    // Select 11 routes in3 to out.
    check_sel_11_routes_in3: assert property (
        @($global_clock) ({sel1, sel0} == 2'b11) |-> (out == in3)
    );

endmodule