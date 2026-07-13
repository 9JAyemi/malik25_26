module bitwise_and_sva (
    input logic CLK,
    input logic [3:0] DATA_IN,
    input logic [3:0] MASK,
    input logic [3:0] DATA_OUT
);
    // Output equals bitwise AND of DATA_IN and MASK.
    check_output_is_bitwise_and: assert property (
        @(posedge CLK) DATA_OUT == (DATA_IN & MASK)
    );

    // When MASK is all zeros, output must be zero.
    check_zero_mask_clears_output: assert property (
        @(posedge CLK) (MASK == 4'b0000) |-> (DATA_OUT == 4'b0000)
    );

    // When MASK is all ones, output equals input.
    check_allones_mask_passthrough: assert property (
        @(posedge CLK) (MASK == 4'b1111) |-> (DATA_OUT == DATA_IN)
    );

    // Bits not selected by MASK must be zero.
    check_unmasked_bits_are_zero: assert property (
        @(posedge CLK) (DATA_OUT & ~MASK) == 4'b0000
    );

    // On masked bits, output matches input.
    check_masked_bits_match_input: assert property (
        @(posedge CLK) ((DATA_OUT ^ DATA_IN) & MASK) == 4'b0000
    );

    // Output cannot introduce new 1s where input has 0s.
    check_no_new_ones_compared_to_input: assert property (
        @(posedge CLK) (DATA_OUT & ~DATA_IN) == 4'b0000
    );
endmodule