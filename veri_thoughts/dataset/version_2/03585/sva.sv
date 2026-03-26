module top_module_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic select,
    input logic out
);

    // With select low and inputs 00, the output is low.
    check_select0_a0_b0_out0: assert property (
        @(posedge clk) (!select && !a && !b) |-> (out == 1'b0)
    );

    // With select low and inputs 01, the output is high.
    check_select0_a0_b1_out1: assert property (
        @(posedge clk) (!select && !a && b) |-> (out == 1'b1)
    );

    // With select low and inputs 10, the output is high.
    check_select0_a1_b0_out1: assert property (
        @(posedge clk) (!select && a && !b) |-> (out == 1'b1)
    );

    // With select low and inputs 11, the output is low.
    check_select0_a1_b1_out0: assert property (
        @(posedge clk) (!select && a && b) |-> (out == 1'b0)
    );

    // With select high and inputs 00, the output is low.
    check_select1_a0_b0_out0: assert property (
        @(posedge clk) (select && !a && !b) |-> (out == 1'b0)
    );

    // With select high and inputs 01, the output is high.
    check_select1_a0_b1_out1: assert property (
        @(posedge clk) (select && !a && b) |-> (out == 1'b1)
    );

    // With select high and inputs 10, the output is high.
    check_select1_a1_b0_out1: assert property (
        @(posedge clk) (select && a && !b) |-> (out == 1'b1)
    );

    // With select high and inputs 11, the output is low.
    check_select1_a1_b1_out0: assert property (
        @(posedge clk) (select && a && b) |-> (out == 1'b0)
    );

endmodule