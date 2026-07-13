module desxor1_sva (
    input logic        clk,
    input logic [47:0] e,
    input logic [47:0] k,
    input logic [5:0]  b1x,
    input logic [5:0]  b2x,
    input logic [5:0]  b3x,
    input logic [5:0]  b4x,
    input logic [5:0]  b5x,
    input logic [5:0]  b6x,
    input logic [5:0]  b7x,
    input logic [5:0]  b8x
);

    // Combinational RTL with no reset; sample behavior on clk.

    // The eight 6-bit outputs reconstruct the full XOR result.
    check_full_xor_mapping: assert property (
        @(posedge clk) {b8x, b7x, b6x, b5x, b4x, b3x, b2x, b1x} == (k ^ e)
    );

    // b1x carries XOR bits [5:0].
    check_b1x_slice: assert property (
        @(posedge clk) b1x == (k[5:0] ^ e[5:0])
    );

    // b2x carries XOR bits [11:6].
    check_b2x_slice: assert property (
        @(posedge clk) b2x == (k[11:6] ^ e[11:6])
    );

    // b3x carries XOR bits [17:12].
    check_b3x_slice: assert property (
        @(posedge clk) b3x == (k[17:12] ^ e[17:12])
    );

    // b4x carries XOR bits [23:18].
    check_b4x_slice: assert property (
        @(posedge clk) b4x == (k[23:18] ^ e[23:18])
    );

    // b5x carries XOR bits [29:24].
    check_b5x_slice: assert property (
        @(posedge clk) b5x == (k[29:24] ^ e[29:24])
    );

    // b6x carries XOR bits [35:30].
    check_b6x_slice: assert property (
        @(posedge clk) b6x == (k[35:30] ^ e[35:30])
    );

    // b7x carries XOR bits [41:36].
    check_b7x_slice: assert property (
        @(posedge clk) b7x == (k[41:36] ^ e[41:36])
    );

    // b8x carries XOR bits [47:42].
    check_b8x_slice: assert property (
        @(posedge clk) b8x == (k[47:42] ^ e[47:42])
    );

endmodule