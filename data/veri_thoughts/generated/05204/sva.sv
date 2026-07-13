module mux4to1_sva(
    input logic in0,
    input logic in1,
    input logic in2,
    input logic in3,
    input logic sel0,
    input logic sel1,
    input logic out
);

    // When select is 00, output routes in0.
    check_sel_00_routes_in0: assert property (
        @($global_clock) ({sel1, sel0} == 2'b00) |-> (out == in0)
    );

    // When select is 01, output routes in1.
    check_sel_01_routes_in1: assert property (
        @($global_clock) ({sel1, sel0} == 2'b01) |-> (out == in1)
    );

    // When select is 10, output routes in2.
    check_sel_10_routes_in2: assert property (
        @($global_clock) ({sel1, sel0} == 2'b10) |-> (out == in2)
    );

    // When select is 11, output routes in3.
    check_sel_11_routes_in3: assert property (
        @($global_clock) ({sel1, sel0} == 2'b11) |-> (out == in3)
    );

endmodule