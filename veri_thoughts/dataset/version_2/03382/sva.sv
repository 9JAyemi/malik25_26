module bin2gray_sva (
    input logic       clk,
    input logic [3:0] bin,
    input logic [3:0] gray
);

    // gray[0] is a direct copy of bin[0].
    check_gray_bit0_passthrough: assert property (
        @(posedge clk) gray[0] == bin[0]
    );

    // gray[1] is the XOR of bin[0] and bin[1].
    check_gray_bit1_xor: assert property (
        @(posedge clk) gray[1] == (bin[0] ^ bin[1])
    );

    // gray[2] matches the RTL XOR chain of w2 and w1.
    check_gray_bit2_xor_chain: assert property (
        @(posedge clk) gray[2] == ((bin[1] ^ bin[2]) ^ (bin[0] ^ bin[1]))
    );

    // gray[3] matches the RTL XOR chain of w3, w2, and bin[3].
    check_gray_bit3_xor_chain: assert property (
        @(posedge clk) gray[3] == ((bin[2] ^ bin[3]) ^ (bin[1] ^ bin[2]) ^ bin[3])
    );

    // The full gray bus matches the implemented bit equations.
    check_gray_vector_function: assert property (
        @(posedge clk) gray == {
            ((bin[2] ^ bin[3]) ^ (bin[1] ^ bin[2]) ^ bin[3]),
            ((bin[1] ^ bin[2]) ^ (bin[0] ^ bin[1])),
            (bin[0] ^ bin[1]),
            bin[0]
        }
    );

endmodule