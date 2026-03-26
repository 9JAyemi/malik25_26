module barrel_shifter_sva (
    input logic [15:0] in,
    input logic [3:0]  shift_amount,
    input logic [15:0] out
);

    // Output always matches the implemented left shift.
    check_out_matches_left_shift: assert property (
        @($global_clock) out == (in << shift_amount)
    );

    // A zero shift leaves the input unchanged.
    check_zero_shift_passthrough: assert property (
        @($global_clock) (shift_amount == 4'd0) |-> (out == in)
    );

    // Any nonzero shift clears the least-significant output bit.
    check_nonzero_shift_clears_lsb: assert property (
        @($global_clock) (shift_amount != 4'd0) |-> (out[0] == 1'b0)
    );

    // A shift of two or more clears the two least-significant output bits.
    check_shift_two_or_more_clears_two_lsbs: assert property (
        @($global_clock) (shift_amount >= 4'd2) |-> (out[1:0] == 2'b00)
    );

    // A shift of eight or more clears the low output byte.
    check_large_shift_clears_low_byte: assert property (
        @($global_clock) (shift_amount >= 4'd8) |-> (out[7:0] == 8'h00)
    );

    // The maximum shift keeps only input bit 0 in the top output bit.
    check_max_shift_behavior: assert property (
        @($global_clock) (shift_amount == 4'd15) |-> (out == {in[0], 15'h0000})
    );

    // A zero input always produces a zero output.
    check_zero_input_produces_zero_output: assert property (
        @($global_clock) (in == 16'h0000) |-> (out == 16'h0000)
    );

endmodule