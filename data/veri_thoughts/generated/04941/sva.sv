module binary_to_gray_sva (
    input logic       clk,
    input logic [7:0] binary,
    input logic [7:0] gray
);

    // The gray bus matches the implemented binary-to-gray conversion.
    check_gray_matches_conversion: assert property (
        @(posedge clk) gray == (binary ^ {1'b0, binary[7:1]})
    );

    // The gray MSB is passed through from the binary MSB.
    check_gray_bit7_passthrough: assert property (
        @(posedge clk) gray[7] == binary[7]
    );

    // Gray bit 6 is binary[6] XOR binary[7].
    check_gray_bit6_xor: assert property (
        @(posedge clk) gray[6] == (binary[6] ^ binary[7])
    );

    // Gray bit 5 is binary[5] XOR binary[6].
    check_gray_bit5_xor: assert property (
        @(posedge clk) gray[5] == (binary[5] ^ binary[6])
    );

    // Gray bit 4 is binary[4] XOR binary[5].
    check_gray_bit4_xor: assert property (
        @(posedge clk) gray[4] == (binary[4] ^ binary[5])
    );

    // Gray bit 3 is binary[3] XOR binary[4].
    check_gray_bit3_xor: assert property (
        @(posedge clk) gray[3] == (binary[3] ^ binary[4])
    );

    // Gray bit 2 is binary[2] XOR binary[3].
    check_gray_bit2_xor: assert property (
        @(posedge clk) gray[2] == (binary[2] ^ binary[3])
    );

    // Gray bit 1 is binary[1] XOR binary[2].
    check_gray_bit1_xor: assert property (
        @(posedge clk) gray[1] == (binary[1] ^ binary[2])
    );

    // Gray bit 0 is binary[0] XOR binary[1].
    check_gray_bit0_xor: assert property (
        @(posedge clk) gray[0] == (binary[0] ^ binary[1])
    );

endmodule