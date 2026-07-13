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

// b1x is the lower 6 bits of e XOR k.
    check_b1x_slice: assert property (
        @(posedge clk) b1x == (e[5:0] ^ k[5:0])
    );

// b2x is the next 6 bits of e XOR k.
    check_b2x_slice: assert property (
        @(posedge clk) b2x == (e[11:6] ^ k[11:6])
    );

// b3x is the next 6 bits of e XOR k.
    check_b3x_slice: assert property (
        @(posedge clk) b3x == (e[17:12] ^ k[17:12])
    );

// b4x is the next 6 bits of e XOR k.
    check_b4x_slice: assert property (
        @(posedge clk) b4x == (e[23:18] ^ k[23:18])
    );

// b5x is the next 6 bits of e XOR k.
    check_b5x_slice: assert property (
        @(posedge clk) b5x == (e[29:24] ^ k[29:24])
    );

// b6x is the next 6 bits of e XOR k.
    check_b6x_slice: assert property (
        @(posedge clk) b6x == (e[35:30] ^ k[35:30])
    );

// b7x is the next 6 bits of e XOR k.
    check_b7x_slice: assert property (
        @(posedge clk) b7x == (e[41:36] ^ k[41:36])
    );

// b8x is the upper 6 bits of e XOR k.
    check_b8x_slice: assert property (
        @(posedge clk) b8x == (e[47:42] ^ k[47:42])
    );

endmodule
