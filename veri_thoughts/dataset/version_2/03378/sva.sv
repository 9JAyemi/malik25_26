module top_module_assertions (
    input logic        clk,
    input logic [15:0] in,
    input logic [7:0]  out_hi,
    input logic [7:0]  out_lo,
    input logic [8:0]  out_parity,
    input logic [7:0]  out_or
);

    // Upper-byte output matches input[15:8].
    check_out_hi_matches_input_upper: assert property (
        @(posedge clk) out_hi == in[15:8]
    );

    // Lower-byte output matches input[7:0].
    check_out_lo_matches_input_lower: assert property (
        @(posedge clk) out_lo == in[7:0]
    );

    // Parity output data field matches input[7:0].
    check_out_parity_data_matches_input_lower: assert property (
        @(posedge clk) out_parity[7:0] == in[7:0]
    );

    // Parity output data field matches the lower-byte output.
    check_out_parity_data_matches_out_lo: assert property (
        @(posedge clk) out_parity[7:0] == out_lo
    );

    // Parity bit equals the reduction XOR of the parity data field.
    check_out_parity_bit_matches_data_xor: assert property (
        @(posedge clk) out_parity[8] == ^out_parity[7:0]
    );

    // Full parity vector has zero overall reduction XOR.
    check_out_parity_vector_even_xor: assert property (
        @(posedge clk) (^out_parity) == 1'b0
    );

    // out_or is the bitwise inverse of the lower-byte output.
    check_out_or_is_inverse_of_out_lo: assert property (
        @(posedge clk) out_or == ~out_lo
    );

    // out_or matches the inverted lower byte of the input.
    check_out_or_matches_inverted_input_lower: assert property (
        @(posedge clk) out_or == ~in[7:0]
    );

endmodule