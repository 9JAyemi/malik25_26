module johnson_counter_and_sva (
    input logic clk,
    input logic reset,
    input logic [7:0] input_val,
    input logic [63:0] output_val
);

    // Reset clears the counter and the output.
    check_reset_clears_output: assert property (
        @(posedge clk) reset |=> (output_val == 64'h0000000000000000)
    );

    // The output is always the counter masked by the replicated input value.
    check_output_matches_mask: assert property (
        @(posedge clk) disable iff (reset)
        output_val == (64'h00000000000000FF << {input_val[3:0], 4'h0})
    );

    // The output is always a zero-extended 8-bit value.
    check_output_upper_bits_zero: assert property (
        @(posedge clk) disable iff (reset)
        output_val[63:8] == 56'h000000000000
    );

    // The output is always a multiple of 256.
    check_output_multiple_of_256: assert property (
        @(posedge clk) disable iff (reset)
        output_val[7:0] == 8'h00
    );

    // The output is always even.
    check_output_even: assert property (
        @(posedge clk) disable iff (reset)
        output_val[0] == 1'b0
    );

    // The output is always a multiple of 16.
    check_output_multiple_of_16: assert property (
        @(posedge clk) disable iff (reset)
        output_val[3:0] == 4'h0
    );

    // The output is always a multiple of 32.
    check_output_multiple_of_32: assert property (
        @(posedge clk) disable iff (reset)
        output_val[4:0] == 5'h0
    );

    // The output is always a multiple of 64.
    check_output_multiple_of_64: assert property (
        @(posedge clk) disable iff (reset)
        output_val[5:0] == 6'h0
    );

    // The output is always a multiple of 128.
    check_output_multiple_of_128: assert property (
        @(posedge clk) disable iff (reset)
        output_val[6:0] == 7'h0
    );

    // The output is always a multiple of 256.
    check_output_multiple_of_256: assert property (
        @(posedge clk) disable iff (reset)
        output_val[7:0] == 8'h00
    );

endmodule