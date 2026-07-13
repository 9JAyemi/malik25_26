module mux4to1_sva (
    input logic clk,
    input logic in0,
    input logic in1,
    input logic in2,
    input logic in3,
    input logic sel0,
    input logic sel1,
    input logic out
);

    // out must match the RTL mux equation.
    check_mux_equation: assert property (
        @(posedge clk)
        out == ((sel1 & sel0) ? in3 :
                ((sel1 & ~sel0) ? in2 :
                 ((~sel1 & sel0) ? in1 : in0)))
    );

    // When sel1 and sel0 are both high, out must select in3.
    check_select_in3: assert property (
        @(posedge clk)
        (sel1 && sel0) |-> (out == in3)
    );

    // When sel1 is high and sel0 is low, out must select in2.
    check_select_in2: assert property (
        @(posedge clk)
        (sel1 && !sel0) |-> (out == in2)
    );

    // When sel1 is low and sel0 is high, out must select in1.
    check_select_in1: assert property (
        @(posedge clk)
        (!sel1 && sel0) |-> (out == in1)
    );

    // When sel1 and sel0 are both low, out must select in0.
    check_select_in0: assert property (
        @(posedge clk)
        (!sel1 && !sel0) |-> (out == in0)
    );

endmodule