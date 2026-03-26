module MUX4_sva (
    input logic in0,
    input logic in1,
    input logic in2,
    input logic in3,
    input logic sel0,
    input logic sel1,
    input logic out
);

    // out equals in0 when the select value is 00.
    check_sel_00_routes_in0: assert property (
        @($global_clock) ({sel1, sel0} == 2'b00) |-> (out == in0)
    );

    // out equals in1 when the select value is 01.
    check_sel_01_routes_in1: assert property (
        @($global_clock) ({sel1, sel0} == 2'b01) |-> (out == in1)
    );

    // out equals in2 when the select value is 10.
    check_sel_10_routes_in2: assert property (
        @($global_clock) ({sel1, sel0} == 2'b10) |-> (out == in2)
    );

    // out equals in3 when the select value is 11.
    check_sel_11_routes_in3: assert property (
        @($global_clock) ({sel1, sel0} == 2'b11) |-> (out == in3)
    );

endmodule