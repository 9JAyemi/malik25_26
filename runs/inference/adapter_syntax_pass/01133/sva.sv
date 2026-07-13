module address_to_signal_sva (
    input logic [9:0]  address,
    input logic        clock,
    input logic [11:0] q
);

    // q must always equal the RTL's concatenation and conditional inversion.
    check_q_matches_rtl_function: assert property (
        @($global_clock)
        q == ({address, 2'b00} ^ {12{clock}})
    );

    // When clock is low, q must equal the shifted address.
    check_q_when_clock_low: assert property (
        @($global_clock)
        !clock |-> (q == {address, 2'b00})
    );

    // When clock is high, q must be the bitwise inverse of the shifted address.
    check_q_when_clock_high: assert property (
        @($global_clock)
        clock |-> (q == ~{address, 2'b00})
    );

    // The upper 10 bits of q must always mirror address.
    check_upper_bits_match_address: assert property (
        @($global_clock)
        q[11:2] == address
    );

    // The low two bits of q must always be zero.
    check_low_bits_zero: assert property (
        @($global_clock)
        q[1:0] == 2'b00
    );

endmodule