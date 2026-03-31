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

    // Output matches the implemented mux tree.
    check_mux_tree_function: assert property (
        @(posedge clk)
        out == (sel1 ? (sel0 ? in3 : in2) : (sel0 ? in1 : in0))
    );

    // When sel1 is low, the output selects between in0 and in1.
    check_sel1_low_selects_low_pair: assert property (
        @(posedge clk)
        !sel1 |-> (out == (sel0 ? in1 : in0))
    );

    // When sel1 is high, the output selects between in2 and in3.
    check_sel1_high_selects_high_pair: assert property (
        @(posedge clk)
        sel1 |-> (out == (sel0 ? in3 : in2))
    );

    // When sel0 is low, the output selects between in0 and in2.
    check_sel0_low_selects_even_inputs: assert property (
        @(posedge clk)
        !sel0 |-> (out == (sel1 ? in2 : (sel1 ? in3 : in0)))
    );

    // When sel0 is high, the output selects between in1 and in3.
    check_sel0_high_selects_odd_inputs: assert property (
        @(posedge clk)
        sel0 |-> (out == (sel1 ? in3 : (sel1 ? in1 : in2)))
    );

    // With sel1 low and sel0 low, the output is in0.
    check_sel10_selects_in0: assert property (
        @(posedge clk)
        (!sel1 && !sel0) |-> (out == in0)
    );

    // With sel1 low and sel0 high, the output is in1.
    check_sel10_selects_in1: assert property (
        @(posedge clk)
        (!sel1 && sel0) |-> (out == in1)
    );

    // With sel1 high and sel0 low, the output is in2.
    check_sel11_selects_in2: assert property (
        @(posedge clk)
        (sel1 && !sel0) |-> (out == in2)
    );

    // With sel1 high and sel0 high, the output is in3.
    check_sel11_selects_in3: assert property (
        @(posedge clk)
        (sel1 && sel0) |-> (out == in3)
    );

endmodule