module adder_sva (
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [8:0] sum
);

    // sum must equal the 8-bit addition of A and B.
    check_sum_matches_addition: assert property (
        @($global_clock) sum == ({1'b0, A} + {1'b0, B})
    );

    // sum[7:0] must equal the low 8 bits of A plus B.
    check_sum_low_bits_match: assert property (
        @($global_clock) sum[7:0] == (A + B)
    );

    // sum[8] must be the carry-out of the 8-bit addition.
    check_sum_msb_is_carry: assert property (
        @($global_clock) sum[8] == (({1'b0, A} + {1'b0, B}) >= 9'h100)
    );

    // sum must never exceed the maximum 8-bit addition result.
    check_sum_is_within_range: assert property (
        @($global_clock) sum <= 9'h1FF
    );

endmodule