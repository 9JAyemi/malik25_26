module v1ea21d_sva (
    input logic clk,
    input logic v27dec4,
    input logic v82de4f,
    input logic v4642b6,
    input logic v0ef266
);

    // External sampling clock; the RTL has no clock or reset.

    // v4642b6 is the OR of the two inputs.
    check_or_function: assert property (
        @(posedge clk) v4642b6 === (v27dec4 | v82de4f)
    );

    // v0ef266 is the NAND of the two inputs.
    check_nand_function: assert property (
        @(posedge clk) v0ef266 === ~(v27dec4 & v82de4f)
    );

    // Both low inputs produce OR=0 and NAND=1.
    check_both_inputs_low_case: assert property (
        @(posedge clk)
        ((v27dec4 === 1'b0) && (v82de4f === 1'b0))
        |-> ((v4642b6 === 1'b0) && (v0ef266 === 1'b1))
    );

    // Both high inputs produce OR=1 and NAND=0.
    check_both_inputs_high_case: assert property (
        @(posedge clk)
        ((v27dec4 === 1'b1) && (v82de4f === 1'b1))
        |-> ((v4642b6 === 1'b1) && (v0ef266 === 1'b0))
    );

    // Differing inputs produce both outputs high.
    check_inputs_differ_case: assert property (
        @(posedge clk)
        (((v27dec4 === 1'b0) && (v82de4f === 1'b1)) ||
         ((v27dec4 === 1'b1) && (v82de4f === 1'b0)))
        |-> ((v4642b6 === 1'b1) && (v0ef266 === 1'b1))
    );

    // The two outputs are never both low.
    check_outputs_never_both_low: assert property (
        @(posedge clk) !((v4642b6 === 1'b0) && (v0ef266 === 1'b0))
    );

    // OR low implies both inputs are low.
    check_or_low_means_inputs_low: assert property (
        @(posedge clk)
        (v4642b6 === 1'b0)
        |-> ((v27dec4 === 1'b0) && (v82de4f === 1'b0))
    );

    // NAND low implies both inputs are high.
    check_nand_low_means_inputs_high: assert property (
        @(posedge clk)
        (v0ef266 === 1'b0)
        |-> ((v27dec4 === 1'b1) && (v82de4f === 1'b1))
    );

endmodule