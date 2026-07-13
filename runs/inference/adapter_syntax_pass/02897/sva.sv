module mux4_sva (
    input logic [3:0] in0,
    input logic [3:0] in1,
    input logic [3:0] in2,
    input logic [3:0] in3,
    input logic       sel0,
    input logic       sel1,
    input logic [3:0] out
);

    // out must match the RTL mux equation.
    check_mux_equation: assert property (
        @($global_clock)
        out == (sel1 & sel0 ? in3 :
                (sel1 & ~sel0 ? in2 :
                 (~sel1 & sel0 ? in1 : in0)))
    );

    // When sel1 and sel0 are both high, out must select in3.
    check_select_in3: assert property (
        @($global_clock)
        (sel1 && sel0) |-> (out == in3)
    );

    // When sel1 is high and sel0 is low, out must select in2.
    check_select_in2: assert property (
        @($global_clock)
        (sel1 && !sel0) |-> (out == in2)
    );

    // When sel1 is low and sel0 is high, out must select in1.
    check_select_in1: assert property (
        @($global_clock)
        (!sel1 && sel0) |-> (out == in1)
    );

    // When both select bits are low, out must select in0.
    check_select_in0: assert property (
        @($global_clock)
        (!sel1 && !sel0) |-> (out == in0)
    );

endmodule