module parity_checker_sva (
    input logic [2:0] data,
    input logic parity
);

    // No RTL clock or reset; this combinational check is sampled on the formal global clock.
    // data is the 3-bit input and parity is the XOR of all three bits.

    // parity must always match the combinational XOR of the three data bits.
    check_parity_xor: assert property (
        @($global_clock) parity == (data[0] ^ data[1] ^ data[2])
    );

endmodule