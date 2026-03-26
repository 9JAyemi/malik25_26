module bitwise_or_and_adder_assertions (
    input logic [15:0] in1,
    input logic [15:0] in2,
    input logic [16:0] res
);

    // No RTL clock or reset; this DUT is purely combinational and sampled on the global clock.

    // Full result must be the zero-extended bitwise OR of the inputs.
    check_full_result_matches_or: assert property (
        @($global_clock) res == {1'b0, (in1 | in2)}
    );

    // Lower 16 result bits must match the bitwise OR of the inputs.
    check_lower_bits_match_or: assert property (
        @($global_clock) res[15:0] == (in1 | in2)
    );

    // The top result bit is tied low.
    check_msb_tied_low: assert property (
        @($global_clock) res[16] == 1'b0
    );

    // When in2 is zero, the result must pass through in1 with a zero MSB.
    check_in1_passthrough_when_in2_zero: assert property (
        @($global_clock) (in2 == 16'h0000) |-> (res == {1'b0, in1})
    );

    // When in1 is zero, the result must pass through in2 with a zero MSB.
    check_in2_passthrough_when_in1_zero: assert property (
        @($global_clock) (in1 == 16'h0000) |-> (res == {1'b0, in2})
    );

endmodule