module four_bit_adder_sva (
    input logic CLK,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] S
);
    // No clock/reset in DUT; this checker samples on external CLK.
    // Logic is purely combinational; key behavior: S == (A ^ B).

    // S must equal bitwise XOR of A and B (bus-level).
    check_sum_is_bitwise_xor: assert property (
        @(posedge CLK) S == (A ^ B)
    );

    // Bit 0: S[0] equals A[0] XOR B[0].
    check_sum_bit0_is_xor: assert property (
        @(posedge CLK) S[0] == (A[0] ^ B[0])
    );

    // Bit 1: S[1] equals A[1] XOR B[1].
    check_sum_bit1_is_xor: assert property (
        @(posedge CLK) S[1] == (A[1] ^ B[1])
    );

    // Bit 2: S[2] equals A[2] XOR B[2].
    check_sum_bit2_is_xor: assert property (
        @(posedge CLK) S[2] == (A[2] ^ B[2])
    );

    // Bit 3: S[3] equals A[3] XOR B[3].
    check_sum_bit3_is_xor: assert property (
        @(posedge CLK) S[3] == (A[3] ^ B[3])
    );

    // If inputs are stable, output must be stable on the next cycle.
    check_sum_stable_when_inputs_stable: assert property (
        @(posedge CLK) ($stable(A) && $stable(B)) |=> $stable(S)
    );

    // Bit 0: equal inputs imply sum bit is 0.
    check_bit0_zero_when_inputs_equal: assert property (
        @(posedge CLK) (A[0] == B[0]) |-> (S[0] == 1'b0)
    );

    // Bit 1: equal inputs imply sum bit is 0.
    check_bit1_zero_when_inputs_equal: assert property (
        @(posedge CLK) (A[1] == B[1]) |-> (S[1] == 1'b0)
    );

    // Bit 2: equal inputs imply sum bit is 0.
    check_bit2_zero_when_inputs_equal: assert property (
        @(posedge CLK) (A[2] == B[2]) |-> (S[2] == 1'b0)
    );

    // Bit 3: equal inputs imply sum bit is 0.
    check_bit3_zero_when_inputs_equal: assert property (
        @(posedge CLK) (A[3] == B[3]) |-> (S[3] == 1'b0)
    );

    // Bit 0: unequal inputs imply sum bit is 1.
    check_bit0_one_when_inputs_unequal: assert property (
        @(posedge CLK) (A[0] != B[0]) |-> (S[0] == 1'b1)
    );

    // Bit 1: unequal inputs imply sum bit is 1.
    check_bit1_one_when_inputs_unequal: assert property (
        @(posedge CLK) (A[1] != B[1]) |-> (S[1] == 1'b1)
    );

    // Bit 2: unequal inputs imply sum bit is 1.
    check_bit2_one_when_inputs_unequal: assert property (
        @(posedge CLK) (A[2] != B[2]) |-> (S[2] == 1'b1)
    );

    // Bit 3: unequal inputs imply sum bit is 1.
    check_bit3_one_when_inputs_unequal: assert property (
        @(posedge CLK) (A[3] != B[3]) |-> (S[3] == 1'b1)
    );

endmodule