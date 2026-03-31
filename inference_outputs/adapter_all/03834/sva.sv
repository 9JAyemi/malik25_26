module barrel_shifter_sva (
    input logic [3:0] D,
    input logic [1:0] A,
    input logic [3:0] S
);

    // A=00 passes D through unchanged.
    check_shift_00_passthrough: assert property (
        @($global_clock) (A == 2'b00) |-> (S == D)
    );

    // A=01 shifts left by 1 and inserts 0 in bit 0.
    check_shift_01_left1_zero: assert property (
        @($global_clock) (A == 2'b01) |-> (S == {D[2:0], 1'b0})
    );

    // A=10 shifts left by 2 and inserts 00 in bits 1:0.
    check_shift_10_left2_zero: assert property (
        @($global_clock) (A == 2'b10) |-> (S == {D[1:0], 2'b00})
    );

    // A=11 shifts left by 3 and inserts 000 in bits 2:0.
    check_shift_11_left3_zero: assert property (
        @($global_clock) (A == 2'b11) |-> (S == {D[0], 3'b000})
    );

    // For A=01, the upper two bits come from D[2:1].
    check_shift_01_upper_bits: assert property (
        @($global_clock) (A == 2'b01) |-> (S[3:2] == D[2:1])
    );

    // For A=01, the lower bit is always 0.
    check_shift_01_lower_zero: assert property (
        @($global_clock) (A == 2'b01) |-> (S[0] == 1'b0)
    );

    // For A=10, the upper bit comes from D[1].
    check_shift_10_upper_bit: assert property (
        @($global_clock) (A == 2'b10) |-> (S[3] == D[1])
    );

    // For A=10, the lower two bits are always 0.
    check_shift_10_lower_zero: assert property (
        @($global_clock) (A == 2'b10) |-> (S[1:0] == 2'b00)
    );

    // For A=11, the upper three bits come from D[2:0].
    check_shift_11_upper_bits: assert property (
        @($global_clock) (A == 2'b11) |-> (S[3:1] == D[2:0])
    );

    // For A=11, the least significant bit is always 0.
    check_shift_11_lower_zero: assert property (
        @($global_clock) (A == 2'b11) |-> (S[0] == 1'b0)
    );

endmodule