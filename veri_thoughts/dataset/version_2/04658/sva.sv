module binaryToGray_sva (
    input logic clk,
    input logic [3:0] binary_input,
    input logic [3:0] gray_output
);

    // DUT is combinational with no reset; sample outputs on clk.

    // Gray bit 0 directly matches binary bit 0.
    check_gray_bit0: assert property (
        @(posedge clk) gray_output[0] == binary_input[0]
    );

    // Gray bit 1 is the XOR of binary bits 0 and 1.
    check_gray_bit1: assert property (
        @(posedge clk) gray_output[1] == (binary_input[0] ^ binary_input[1])
    );

    // Gray bit 2 is the XOR of binary bits 1 and 2.
    check_gray_bit2: assert property (
        @(posedge clk) gray_output[2] == (binary_input[1] ^ binary_input[2])
    );

    // Gray bit 3 is the XOR of binary bits 2 and 3.
    check_gray_bit3: assert property (
        @(posedge clk) gray_output[3] == (binary_input[2] ^ binary_input[3])
    );

    // The full output vector matches the implemented binary-to-gray mapping.
    check_gray_vector: assert property (
        @(posedge clk) gray_output == {binary_input[2] ^ binary_input[3],
                                      binary_input[1] ^ binary_input[2],
                                      binary_input[0] ^ binary_input[1],
                                      binary_input[0]}
    );

endmodule