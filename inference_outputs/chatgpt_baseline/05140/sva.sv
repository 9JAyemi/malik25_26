module four_bit_adder_sva (
    input logic [3:0] S,
    input logic CO,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic CI
);

    function automatic logic fa_carry (
        input logic a,
        input logic b,
        input logic carry_in
    );
        fa_carry = (a & b) | (a & carry_in) | (b & carry_in);
    endfunction

    // The 5-bit output matches A + B + CI.
    check_full_sum_relation: assert property (
        @($global_clock) {CO, S} == ({1'b0, A} + {1'b0, B} + CI)
    );

    // Bit 0 sum matches the first full-adder XOR equation.
    check_sum_bit0_relation: assert property (
        @($global_clock) S[0] == (A[0] ^ B[0] ^ CI)
    );

    // Bit 1 sum uses the carry from bit 0.
    check_sum_bit1_relation: assert property (
        @($global_clock) S[1] == (A[1] ^ B[1] ^ fa_carry(A[0], B[0], CI))
    );

    // Bit 2 sum uses the carry chain through bits 0 and 1.
    check_sum_bit2_relation: assert property (
        @($global_clock) S[2] == (A[2] ^ B[2] ^ fa_carry(A[1], B[1], fa_carry(A[0], B[0], CI)))
    );

    // Bit 3 sum uses the carry chain through bits 0, 1, and 2.
    check_sum_bit3_relation: assert property (
        @($global_clock) S[3] == (A[3] ^ B[3] ^ fa_carry(A[2], B[2], fa_carry(A[1], B[1], fa_carry(A[0], B[0], CI))))
    );

    // Carry-out matches the final full-adder carry equation.
    check_carry_out_relation: assert property (
        @($global_clock) CO == fa_carry(A[3], B[3], fa_carry(A[2], B[2], fa_carry(A[1], B[1], fa_carry(A[0], B[0], CI))))
    );

endmodule