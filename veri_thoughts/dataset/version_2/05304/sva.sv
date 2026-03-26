module nor_4bit_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] Z
);

    // Z must be the bitwise NOR of A and B.
    check_z_matches_bitwise_nor: assert property (
        @($global_clock) Z == ~(A | B)
    );

    // Bit 0 output must equal NOR of bit 0 inputs.
    check_bit0_nor_function: assert property (
        @($global_clock) Z[0] == ~(A[0] | B[0])
    );

    // Bit 1 output must equal NOR of bit 1 inputs.
    check_bit1_nor_function: assert property (
        @($global_clock) Z[1] == ~(A[1] | B[1])
    );

    // Bit 2 output must equal NOR of bit 2 inputs.
    check_bit2_nor_function: assert property (
        @($global_clock) Z[2] == ~(A[2] | B[2])
    );

    // Bit 3 output must equal NOR of bit 3 inputs.
    check_bit3_nor_function: assert property (
        @($global_clock) Z[3] == ~(A[3] | B[3])
    );

endmodule