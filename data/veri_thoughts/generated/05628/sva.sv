module top_module_sva (
    input logic clk,
    input logic [15:0] in,
    input logic [7:0] out_hi,
    input logic [7:0] out_lo,
    input logic [7:0] out_sum
);

    // out_hi is the upper byte of in.
    check_high_byte_split: assert property (
        @(posedge clk) out_hi == in[15:8]
    );

    // out_lo is the lower byte of in.
    check_low_byte_split: assert property (
        @(posedge clk) out_lo == in[7:0]
    );

    // The split outputs reconstruct the input.
    check_split_reconstructs_input: assert property (
        @(posedge clk) {out_hi, out_lo} == in
    );

    // out_sum equals the sum of the split outputs.
    check_sum_matches_split_outputs: assert property (
        @(posedge clk) out_sum == (out_hi + out_lo)
    );

    // out_sum equals the sum of the two input bytes.
    check_sum_matches_input_halves: assert property (
        @(posedge clk) out_sum == (in[15:8] + in[7:0])
    );

endmodule