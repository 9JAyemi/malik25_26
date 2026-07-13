module parity_generator_sva (
    input logic [3:0] data,
    input logic parity
);

    // Parity must equal the inverted XOR of all four data bits.
    check_parity_matches_function: assert property (
        @($global_clock) parity == ~(data[0] ^ data[1] ^ data[2] ^ data[3])
    );

    // An even XOR result must produce a high parity output.
    check_even_xor_drives_high: assert property (
        @($global_clock) ((data[0] ^ data[1] ^ data[2] ^ data[3]) == 1'b0) |-> (parity == 1'b1)
    );

    // An odd XOR result must produce a low parity output.
    check_odd_xor_drives_low: assert property (
        @($global_clock) ((data[0] ^ data[1] ^ data[2] ^ data[3]) == 1'b1) |-> (parity == 1'b0)
    );

    // Stable input data must keep the combinational parity output stable.
    check_stable_data_keeps_parity_stable: assert property (
        @($global_clock) $stable(data) |-> $stable(parity)
    );

endmodule