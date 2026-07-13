module MoleDecoder_sva (
    input logic CLK,                 // sampling clock for assertions
    input logic [4:0] mole_position,
    input logic [15:0] mole16bit
);
    // Output has at most one bit set or is all zero.
    check_onehot0_output: assert property (
        @(posedge CLK) $onehot0(mole16bit)
    );

    // For positions 0..15, output equals 1 shifted left by mole_position.
    check_decode_when_valid_position: assert property (
        @(posedge CLK) (mole_position <= 5'd15) |-> (mole16bit == (16'h0001 << mole_position))
    );

    // For positions 16..31, output is zero.
    check_zero_on_invalid_position: assert property (
        @(posedge CLK) (mole_position > 5'd15) |-> (mole16bit == 16'h0000)
    );

    // Zero output implies position is outside 0..15.
    check_zero_means_invalid_position: assert property (
        @(posedge CLK) (mole16bit == 16'h0000) |-> (mole_position > 5'd15)
    );

    // Non-zero output implies position is within 0..15.
    check_nonzero_means_valid_position: assert property (
        @(posedge CLK) (mole16bit != 16'h0000) |-> (mole_position <= 5'd15)
    );

    // Non-zero output must match the 1<<mole_position encoding.
    check_nonzero_matches_shift: assert property (
        @(posedge CLK) (mole16bit != 16'h0000) |-> (mole16bit == (16'h0001 << mole_position))
    );

    // Boundary: position 0 decodes to LSB set.
    check_pos0_maps_to_lsb: assert property (
        @(posedge CLK) (mole_position == 5'd0) |-> (mole16bit == 16'h0001)
    );

    // Boundary: position 15 decodes to MSB set.
    check_pos15_maps_to_msb: assert property (
        @(posedge CLK) (mole_position == 5'd15) |-> (mole16bit == 16'h8000)
    );
endmodule