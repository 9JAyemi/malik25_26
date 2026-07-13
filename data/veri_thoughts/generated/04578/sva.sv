module twos_complement_sva (
    input logic       clk,
    input logic [3:0] in,
    input logic [3:0] out
);

    // RTL is combinational; assertions sample on an external clock.

    // Output is the 4-bit two's complement of the input.
    check_exact_twos_complement: assert property (
        @(posedge clk) out == (~in + 4'b0001)
    );

    // Input and output sum to zero modulo 16.
    check_additive_inverse: assert property (
        @(posedge clk) (in + out) == 4'h0
    );

    // Zero maps to zero.
    check_zero_maps_to_zero: assert property (
        @(posedge clk) (in == 4'h0) |-> (out == 4'h0)
    );

    // 4'b1000 is its own two's complement.
    check_min_value_maps_to_self: assert property (
        @(posedge clk) (in == 4'h8) |-> (out == 4'h8)
    );

    // Positive nonzero inputs produce a negative 4-bit result.
    check_positive_nonzero_sign_flip: assert property (
        @(posedge clk) ((in[3] == 1'b0) && (in != 4'h0)) |-> (out[3] == 1'b1)
    );

    // Negative inputs other than 4'b1000 produce a positive 4-bit result.
    check_negative_nonmin_sign_flip: assert property (
        @(posedge clk) ((in[3] == 1'b1) && (in != 4'h8)) |-> (out[3] == 1'b0)
    );

endmodule