module two_bit_encoder_sva (
    input logic [1:0] data,
    input logic q,
    input logic zero
);

    // q must always mirror the MSB of data.
    check_q_matches_msb: assert property (
        @($global_clock) q == data[1]
    );

    // zero must always indicate that data is 2'b00.
    check_zero_matches_zero_detect: assert property (
        @($global_clock) zero == ~(|data)
    );

    // zero high implies both input bits are low.
    check_zero_implies_data_zero: assert property (
        @($global_clock) zero |-> (data == 2'b00)
    );

    // Any nonzero input must deassert zero.
    check_nonzero_input_clears_zero: assert property (
        @($global_clock) (data != 2'b00) |-> !zero
    );

    // Input 00 must produce q=0 and zero=1.
    check_encode_00: assert property (
        @($global_clock) (data == 2'b00) |-> (!q && zero)
    );

    // Input 01 must produce q=0 and zero=0.
    check_encode_01: assert property (
        @($global_clock) (data == 2'b01) |-> (!q && !zero)
    );

    // Input 10 must produce q=1 and zero=0.
    check_encode_10: assert property (
        @($global_clock) (data == 2'b10) |-> (q && !zero)
    );

    // Input 11 must produce q=1 and zero=0.
    check_encode_11: assert property (
        @($global_clock) (data == 2'b11) |-> (q && !zero)
    );

endmodule