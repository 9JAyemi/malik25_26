module twos_complement_assertions (
    input logic        clk,
    input logic [15:0] in,
    input logic        reset,
    input logic [31:0] out
);

    // Reset forces the output to zero.
    check_reset_clears_out: assert property (
        @(posedge clk) reset |-> (out == 32'h00000000)
    );

    // Outside reset, the output matches the implemented concatenation.
    check_nonreset_output_encoding: assert property (
        @(posedge clk) disable iff (reset) (out == {in, {16{!in[15]}}})
    );

    // Outside reset, the upper 16 bits mirror the input.
    check_nonreset_upper_half_matches_input: assert property (
        @(posedge clk) disable iff (reset) (out[31:16] == in)
    );

    // Outside reset, a set input MSB makes the lower 16 bits all zero.
    check_negative_input_low_half_zero: assert property (
        @(posedge clk) disable iff (reset) in[15] |-> (out[15:0] == 16'h0000)
    );

    // Outside reset, a clear input MSB makes the lower 16 bits all one.
    check_nonnegative_input_low_half_ones: assert property (
        @(posedge clk) disable iff (reset) !in[15] |-> (out[15:0] == 16'hFFFF)
    );

endmodule