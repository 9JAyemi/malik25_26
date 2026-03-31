module rising_edge_detector_sva (
    input logic clk,
    input logic reset,
    input logic [31:0] in,
    input logic [31:0] out
);

    // Reset clears the output on the next clock.
    check_reset_clears_out: assert property (
        @(posedge clk) reset |=> (out == 32'h00000000)
    );

    // A zero input produces a zero output on the next clock.
    check_zero_input_zero_output: assert property (
        @(posedge clk) disable iff (reset) (in == 32'h00000000) |=> (out == 32'h00000000)
    );

    // A zero output implies the input was zero on the prior clock.
    check_zero_output_implies_zero_input: assert property (
        @(posedge clk) disable iff (reset) (out == 32'h00000000) |=> (in == 32'h00000000)
    );

    // A nonzero output implies the input was nonzero on the prior clock.
    check_nonzero_output_implies_nonzero_input: assert property (
        @(posedge clk) disable iff (reset) (out != 32'h00000000) |=> (in != 32'h00000000)
    );

    // A nonzero output is a subset of the prior input.
    check_nonzero_output_subset_of_input: assert property (
        @(posedge clk) disable iff (reset) (out != 32'h00000000) |=> ((out & ~in) == 32'h00000000)
    );

    // A nonzero output cannot overlap bits that were already high on the prior clock.
    check_nonzero_output_no_overlap_with_previous_highs: assert property (
        @(posedge clk) disable iff (reset) (out != 32'h00000000) |=> ((out & ~($past(in) & ~$past(out))) == 32'h00000000)
    );

endmodule