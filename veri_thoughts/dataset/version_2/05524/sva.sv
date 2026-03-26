module bit_checker_sva (
    input logic clk,
    input logic [15:0] in,
    input logic out
);

    // Out equals the reduction OR of the input bus.
    check_out_matches_reduction_or: assert property (
        @(posedge clk) out === (|in)
    );

    // Zero input drives the output low.
    check_zero_input_drives_low: assert property (
        @(posedge clk) ((|in) === 1'b0) |-> (out === 1'b0)
    );

    // Any set input bit drives the output high.
    check_nonzero_input_drives_high: assert property (
        @(posedge clk) ((|in) === 1'b1) |-> (out === 1'b1)
    );

    // A low output means no input bits are set.
    check_low_output_implies_zero_input: assert property (
        @(posedge clk) (out === 1'b0) |-> ((|in) === 1'b0)
    );

    // A high output means at least one input bit is set.
    check_high_output_implies_nonzero_input: assert property (
        @(posedge clk) (out === 1'b1) |-> ((|in) === 1'b1)
    );

endmodule