module binary_to_gray_sva (
    input logic       clk,
    input logic [3:0] b,
    input logic [3:0] g
);

    // Output vector matches the binary-to-Gray transform.
    check_gray_vector_encoding: assert property (
        @(posedge clk) g == ({1'b0, b[3:1]} ^ b)
    );

    // g[3] passes through b[3].
    check_gray_bit3: assert property (
        @(posedge clk) g[3] == b[3]
    );

    // g[2] is b[3] xor b[2].
    check_gray_bit2: assert property (
        @(posedge clk) g[2] == (b[3] ^ b[2])
    );

    // g[1] is b[2] xor b[1].
    check_gray_bit1: assert property (
        @(posedge clk) g[1] == (b[2] ^ b[1])
    );

    // g[0] is b[1] xor b[0].
    check_gray_bit0: assert property (
        @(posedge clk) g[0] == (b[1] ^ b[0])
    );

endmodule