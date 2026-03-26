module top_module_sva (
    input logic        clk,
    input logic [15:0] a,
    input logic [15:0] b,
    input logic [3:0]  shift,
    input logic        select,
    input logic [15:0] out
);

    // No reset exists in the RTL; properties are sampled on an external clock.

    // Output must equal the adder result ORed with its left-shifted version.
    check_output_function: assert property (
        @(posedge clk) (out == ((a + b) | ((a + b) << shift)))
    );

    // When select is high, output still matches the same implemented function.
    check_select_high_function: assert property (
        @(posedge clk) select |-> (out == ((a + b) | ((a + b) << shift)))
    );

    // When select is low, output still matches the same implemented function.
    check_select_low_function: assert property (
        @(posedge clk) !select |-> (out == ((a + b) | ((a + b) << shift)))
    );

    // A zero shift makes the output equal to the adder result.
    check_shift_zero_passthrough: assert property (
        @(posedge clk) (shift == 4'd0) |-> (out == (a + b))
    );

    // Every asserted bit of the adder result must appear in the output.
    check_output_contains_sum_bits: assert property (
        @(posedge clk) (((a + b) & ~out) == 16'h0000)
    );

    // Every asserted bit of the shifted adder result must appear in the output.
    check_output_contains_shifted_sum_bits: assert property (
        @(posedge clk) ((((a + b) << shift) & ~out) == 16'h0000)
    );

    // A zero adder result forces the output low.
    check_zero_sum_gives_zero_out: assert property (
        @(posedge clk) ((a + b) == 16'h0000) |-> (out == 16'h0000)
    );

    // A zero output implies the adder result is also zero.
    check_zero_out_implies_zero_sum: assert property (
        @(posedge clk) (out == 16'h0000) |-> ((a + b) == 16'h0000)
    );

    // Output bit 0 always matches bit 0 of the adder result.
    check_lsb_matches_sum_lsb: assert property (
        @(posedge clk) (out[0] == (a[0] ^ b[0]))
    );

    // For nonzero shifts, the shifted-off low bits remain equal to the adder result.
    check_shifted_off_low_bits_unchanged: assert property (
        @(posedge clk) (shift != 4'd0) |-> ((out & ((16'h0001 << shift) - 16'h0001)) == ((a + b) & ((16'h0001 << shift) - 16'h0001)))
    );

endmodule