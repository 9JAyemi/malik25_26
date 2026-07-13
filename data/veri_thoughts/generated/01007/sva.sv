module gray_code_converter_sva (
    input logic clk,                   // Sampling clock for assertions (DUT has no clock/reset)
    input logic [15:0] binary_input,
    input logic [15:0] gray_code_output
);
    // Output equals binary XOR (binary >> 1) for all bits.
    check_functional_mapping: assert property (
        @(posedge clk) gray_code_output == (binary_input ^ (binary_input >> 1))
    );

    // MSB of Gray equals MSB of Binary.
    check_msb_passthrough: assert property (
        @(posedge clk) gray_code_output[15] == binary_input[15]
    );

    genvar i;
    generate
        for (i = 0; i < 15; i++) begin : gen_bit_map
            // Gray bit[i] equals XOR of binary bits i and i+1.
            check_bitwise_mapping: assert property (
                @(posedge clk) gray_code_output[i] == (binary_input[i] ^ binary_input[i+1])
            );
        end
    endgenerate
endmodule