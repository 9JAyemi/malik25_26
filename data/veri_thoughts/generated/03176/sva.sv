module bin2gray_sva(
    input logic       clk,
    input logic [3:0] binary,
    input logic [3:0] gray
);

    // Full Gray output matches the implemented binary-to-Gray conversion.
    check_gray_vector_mapping: assert property (
        @(posedge clk)
        gray == {binary[3], (binary[3] ^ binary[2]), (binary[2] ^ binary[1]), (binary[1] ^ binary[0])}
    );

    // gray[3] is a direct copy of binary[3].
    check_gray_bit3_passthrough: assert property (
        @(posedge clk)
        gray[3] == binary[3]
    );

    // gray[2] is binary[3] XOR binary[2].
    check_gray_bit2_xor: assert property (
        @(posedge clk)
        gray[2] == (binary[3] ^ binary[2])
    );

    // gray[1] is binary[2] XOR binary[1].
    check_gray_bit1_xor: assert property (
        @(posedge clk)
        gray[1] == (binary[2] ^ binary[1])
    );

    // gray[0] is binary[1] XOR binary[0].
    check_gray_bit0_xor: assert property (
        @(posedge clk)
        gray[0] == (binary[1] ^ binary[0])
    );

endmodule