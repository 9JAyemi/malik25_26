module gray_code_sva (
    input logic [3:0] a,
    input logic [3:0] gray
);

    // MSB of gray matches the MSB of input a.
    check_gray_bit3_passthrough: assert property (
        @($global_clock) gray[3] === a[3]
    );

    // Gray bit 2 is the XOR of input bits 3 and 2.
    check_gray_bit2_xor: assert property (
        @($global_clock) gray[2] === (a[3] ^ a[2])
    );

    // Gray bit 1 is the XOR of input bits 2 and 1.
    check_gray_bit1_xor: assert property (
        @($global_clock) gray[1] === (a[2] ^ a[1])
    );

    // Gray bit 0 is the XOR of input bits 1 and 0.
    check_gray_bit0_xor: assert property (
        @($global_clock) gray[0] === (a[1] ^ a[0])
    );

    // Full gray output matches the RTL combinational encoding.
    check_gray_vector_encoding: assert property (
        @($global_clock) gray === {a[3], (a[3] ^ a[2]), (a[2] ^ a[1]), (a[1] ^ a[0])}
    );

endmodule