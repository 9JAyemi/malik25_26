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

    // b1x is the low 6 bits of k ^ e.
    check_b1x_slice: assert property (
        @(posedge clk) b1x == (k ^ e)[5:0]
    );

    // b2x is bits 11:6 of k ^ e.
    check_b2x_slice: assert property (
        @(posedge clk) b2x == (k ^ e)[11:6]
    );

    // b3x is bits 17:12 of k ^ e.
    check_b3x_slice: assert property (
        @(posedge clk) b3x == (k ^ e)[17:12]
    );

    // b4x is bits 23:18 of k ^ e.
    check_b4x_slice: assert property (
        @(posedge clk) b4x == (k ^ e)[23:18]
    );

    // b5x is bits 29:24 of k ^ e.
    check_b5x_slice: assert property (
        @(posedge clk) b5x == (k ^ e)[29:24]
    );

    // b6x is bits 35:30 of k ^ e.
    check_b6x_slice: assert property (
        @(posedge clk) b6x == (k ^ e)[35:30]
    );

    // b7x is bits 41:36 of k ^ e.
    check_b7x_slice: assert property (
        @(posedge clk) b7x == (k ^ e)[41:36]
    );

    // b8x is the high 6 bits of k ^ e.
    check_b8x_slice: assert property (
        @(posedge clk) b8x == (k ^ e)[47:42]
    );

    // The eight output slices reconstruct the full XOR result.
    check_full_xor_reconstruction: assert property (
        @(posedge clk) {b8x, b7x, b6x, b5x, b4x, b3x, b2x, b1x} == (k ^ e)
    );

endmodule