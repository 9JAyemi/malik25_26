module top_module_sva (
    input logic        clk,
    input logic [15:0] in,
    input logic [7:0]  out_hi,
    input logic [7:0]  out_lo,
    input logic [15:0] final_out
);

    // No RTL clock/reset; clk is only a sampling clock for these checks.
    // Observable behavior is purely combinational on in, out_hi, out_lo, and final_out.

    // out_hi must always equal the upper byte of in.
    check_out_hi_slice: assert property (
        @(posedge clk) out_hi == in[15:8]
    );

    // out_lo must always equal the lower byte of in.
    check_out_lo_slice: assert property (
        @(posedge clk) out_lo == in[7:0]
    );

    // The two byte outputs must reconstruct the input word.
    check_output_bytes_reconstruct_input: assert property (
        @(posedge clk) {out_hi, out_lo} == in
    );

    // final_out upper byte must be zero because the adder sums two 8-bit inputs.
    check_final_out_upper_byte_zero: assert property (
        @(posedge clk) final_out[15:8] == 8'h00
    );

    // final_out lower byte must equal the sum of out_hi and out_lo.
    check_final_out_lower_byte_sum: assert property (
        @(posedge clk) final_out[7:0] == (out_hi + out_lo)
    );

    // final_out must equal the zero-extended sum of the byte outputs.
    check_final_out_matches_output_sum: assert property (
        @(posedge clk) final_out == {8'h00, (out_hi + out_lo)}
    );

    // final_out must equal the zero-extended sum of the input bytes.
    check_final_out_matches_input_bytes: assert property (
        @(posedge clk) final_out == {8'h00, (in[15:8] + in[7:0])}
    );

endmodule