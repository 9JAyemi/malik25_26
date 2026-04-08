module twos_complement_sva(
    input logic [3:0] in,
    input logic [3:0] out
);

    // Output matches the implemented two's complement expression.
    check_out_matches_twos_complement: assert property (
        @($global_clock) out == ((~in) + 4'h1)
    );

    // Input and output are additive inverses modulo 16.
    check_additive_inverse_mod16: assert property (
        @($global_clock) (in + out) == 4'h0
    );

    // Zero maps to zero.
    check_zero_maps_to_zero: assert property (
        @($global_clock) (in == 4'h0) |-> (out == 4'h0)
    );

    // Only zero produces a zero output.
    check_zero_output_implies_zero_input: assert property (
        @($global_clock) (out == 4'h0) |-> (in == 4'h0)
    );

    // 4'b1000 is self-inverse in 4-bit two's complement.
    check_most_negative_self_inverse: assert property (
        @($global_clock) (in == 4'h8) |-> (out == 4'h8)
    );

    // Taking two's complement of the output reconstructs the input.
    check_double_twos_complement_returns_input: assert property (
        @($global_clock) ((~out) + 4'h1) == in
    );

endmodule