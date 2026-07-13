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

// Out must match the RTL mux expression.
    check_mux_function: assert property (
        @(posedge clk)
        out == ((sel1 & sel0) ? in3 :
                (sel1 & ~sel0) ? in2 :
                (~sel1 & sel0) ? in1 :
                in0)
    );

// When sel is 00, out must select in0.
    check_sel_00_selects_in0: assert property (
        @(posedge clk)
        (!sel1 && !sel0) |-> (out == in0)
    );

// When sel is 01, out must select in1.
    check_sel_01_selects_in1: assert property (
        @(posedge clk)
        (!sel1 && sel0) |-> (out == in1)
    );

// When sel is 10, out must select in2.
    check_sel_10_selects_in2: assert property (
        @(posedge clk)
        (sel1 && !sel0) |-> (out == in2)
    );

// When sel is 11, out must select in3.
    check_sel_11_selects_in3: assert property (
        @(posedge clk)
        (sel1 && sel0) |-> (out == in3)
    );

endmodule
