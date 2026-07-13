module invert_msb_sva (
    input logic clk,
    input logic [3:0] i_binary,
    input logic [3:0] o_inverted
);

    // Output must equal the input with only the MSB inverted.
    check_invert_msb_function: assert property (
        @(posedge clk) o_inverted === {~i_binary[3], i_binary[2:0]}
    );

    // Output MSB must be the inverse of the input MSB.
    check_output_msb_inverted: assert property (
        @(posedge clk) o_inverted[3] === ~i_binary[3]
    );

    // Output lower three bits must pass through unchanged.
    check_output_lower_bits_passthrough: assert property (
        @(posedge clk) o_inverted[2:0] === i_binary[2:0]
    );

endmodule