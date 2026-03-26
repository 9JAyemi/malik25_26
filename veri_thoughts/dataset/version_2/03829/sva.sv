module four_to_one_sva (
    input logic clk,
    input logic [3:0] in,
    input logic out
);

    // Output must equal the reduction-OR of the input bus.
    check_out_matches_reduction_or: assert property (
        @(posedge clk) out == (|in)
    );

    // A zero input vector must drive the output low.
    check_zero_input_drives_low: assert property (
        @(posedge clk) (in == 4'b0000) |-> (out == 1'b0)
    );

    // Any non-zero input vector must drive the output high.
    check_nonzero_input_drives_high: assert property (
        @(posedge clk) (in != 4'b0000) |-> (out == 1'b1)
    );

endmodule