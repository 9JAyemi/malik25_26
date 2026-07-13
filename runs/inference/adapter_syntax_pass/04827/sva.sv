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

    // out matches the implemented mux tree.
    check_out_matches_mux_tree: assert property (
        @(posedge clk)
        out == (sel1 ? (sel0 ? in3 : in2) : (sel0 ? in1 : in0))
    );

    // When sel1 is low, out selects between in0 and in1.
    check_sel1_low_selects_in0_in1: assert property (
        @(posedge clk)
        !sel1 |-> (out == (sel0 ? in1 : in0))
    );

    // When sel1 is high, out selects between in2 and in3.
    check_sel1_high_selects_in2_in3: assert property (
        @(posedge clk)
        sel1 |-> (out == (sel0 ? in3 : in2))
    );

    // When sel0 is low, out selects between in0 and in2.
    check_sel0_low_selects_in0_in2: assert property (
        @(posedge clk)
        !sel0 |-> (out == (sel1 ? in2 : in0))
    );

    // When sel0 is high, out selects between in1 and in3.
    check_sel0_high_selects_in1_in3: assert property (
        @(posedge clk)
        sel0 |-> (out == (sel1 ? in3 : in1))
    );

    // With sel1 low and sel0 low, out follows in0.
    check_sel10_selects_in0: assert property (
        @(posedge clk)
        (!sel1 && !sel0) |-> (out == in0)
    );

    // With sel1 low and sel0 high, out follows in1.
    check_sel10_selects_in1: assert property (
        @(posedge clk)
        (!sel1 && sel0) |-> (out == in1)
    );

    // With sel1 high and sel0 low, out follows in2.
    check_sel11_selects_in2: assert property (
        @(posedge clk)
        (sel1 && !sel0) |-> (out == in2)
    );

    // With sel1 high and sel0 high, out follows in3.
    check_sel11_selects_in3: assert property (
        @(posedge clk)
        (sel1 && sel0) |-> (out == in3)
    );

endmodule