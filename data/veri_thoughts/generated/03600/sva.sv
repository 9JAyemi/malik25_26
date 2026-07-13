module twos_comp_sva (
    input logic [3:0] in,
    input logic [3:0] out
);

    // Output matches the 4-bit two's complement of the input.
    check_output_is_twos_complement: assert property (
        @($global_clock) out == (~in + 4'b0001)
    );

    // Input and output sum to zero modulo 16.
    check_additive_inverse_mod16: assert property (
        @($global_clock) (in + out) == 4'b0000
    );

    // Zero input produces zero output.
    check_zero_maps_to_zero: assert property (
        @($global_clock) (in == 4'b0000) |-> (out == 4'b0000)
    );

    // Nonzero inputs sum with their output to 16 in 5-bit arithmetic.
    check_nonzero_wrap_sum_is_16: assert property (
        @($global_clock) (in != 4'b0000) |-> ({1'b0, in} + {1'b0, out} == 5'b1_0000)
    );

    // 4'b1000 is its own two's complement in 4 bits.
    check_most_negative_self_inverse: assert property (
        @($global_clock) (in == 4'b1000) |-> (out == 4'b1000)
    );

endmodule