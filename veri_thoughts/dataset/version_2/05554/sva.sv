module binary_to_gray_converter_sva (
    input logic       clk,
    input logic [3:0] binary_input,
    input logic [3:0] gray_output
);

    // MSB passes through unchanged.
    check_gray_msb_passthrough: assert property (
        @(posedge clk) gray_output[3] === binary_input[3]
    );

    // Bit 2 is binary_input[3] XOR binary_input[2].
    check_gray_bit2_xor: assert property (
        @(posedge clk) gray_output[2] === (binary_input[3] ^ binary_input[2])
    );

    // Bit 1 is binary_input[2] XOR binary_input[1].
    check_gray_bit1_xor: assert property (
        @(posedge clk) gray_output[1] === (binary_input[2] ^ binary_input[1])
    );

    // Bit 0 is binary_input[1] XOR binary_input[0].
    check_gray_lsb_xor: assert property (
        @(posedge clk) gray_output[0] === (binary_input[1] ^ binary_input[0])
    );

    // Full output matches the standard binary-to-Gray conversion.
    check_gray_vector_relation: assert property (
        @(posedge clk) gray_output === (binary_input ^ (binary_input >> 1))
    );

endmodule