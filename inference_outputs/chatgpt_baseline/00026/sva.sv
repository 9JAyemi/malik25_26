module bin2gray_sva (
    input logic clk,
    input logic [3:0] bin,
    input logic [3:0] gray
);

    // gray[3] is a direct copy of bin[3].
    check_gray_bit3_passthrough: assert property (
        @(posedge clk) gray[3] == bin[3]
    );

    // gray[2] is bin[3] XOR bin[2].
    check_gray_bit2_xor: assert property (
        @(posedge clk) gray[2] == (bin[3] ^ bin[2])
    );

    // gray[1] is bin[2] XOR bin[1].
    check_gray_bit1_xor: assert property (
        @(posedge clk) gray[1] == (bin[2] ^ bin[1])
    );

    // gray[0] is bin[1] XOR bin[0].
    check_gray_bit0_xor: assert property (
        @(posedge clk) gray[0] == (bin[1] ^ bin[0])
    );

    // The full gray output matches the implemented conversion.
    check_gray_vector_conversion: assert property (
        @(posedge clk) gray == {bin[3], (bin[3] ^ bin[2]), (bin[2] ^ bin[1]), (bin[1] ^ bin[0])}
    );

endmodule