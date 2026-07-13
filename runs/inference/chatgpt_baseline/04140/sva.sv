module odd_even_sva (
    input logic clk,
    input logic [2:0] input_bits,
    input logic [1:0] output_bits
);

    // An input LSB of 1 must drive output 01.
    check_lsb_one_maps_to_01: assert property (
        @(posedge clk) (input_bits[0] === 1'b1) |-> (output_bits == 2'b01)
    );

    // Any non-1 LSB value must drive output 10.
    check_lsb_not_one_maps_to_10: assert property (
        @(posedge clk) (input_bits[0] !== 1'b1) |-> (output_bits == 2'b10)
    );

    // output_bits[0] reflects whether the LSB is exactly 1.
    check_output_bit0_matches_true_branch: assert property (
        @(posedge clk) output_bits[0] == (input_bits[0] === 1'b1)
    );

    // output_bits[1] reflects the else branch selection.
    check_output_bit1_matches_else_branch: assert property (
        @(posedge clk) output_bits[1] == (input_bits[0] !== 1'b1)
    );

    // The output must always be one of the two assigned encodings.
    check_output_encoding_is_valid: assert property (
        @(posedge clk) ((output_bits == 2'b01) || (output_bits == 2'b10))
    );

endmodule