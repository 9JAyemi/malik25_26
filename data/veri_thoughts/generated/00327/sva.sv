module RCA_4bit_sva (
    input logic       clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] S,
    input logic       Ci,
    input logic       Co
);

    function automatic logic fa_carry (
        input logic a,
        input logic b,
        input logic ci
    );
        fa_carry = (a & b) | (a & ci) | (b & ci);
    endfunction

    // Outputs match 4-bit addition with carry-in.
    check_overall_addition: assert property (
        @(posedge clk) {Co, S} == ({1'b0, A} + {1'b0, B} + {4'b0000, Ci})
    );

    // Bit 0 sum matches the first full-adder sum.
    check_bit0_sum: assert property (
        @(posedge clk) S[0] == (A[0] ^ B[0] ^ Ci)
    );

    // Bit 1 sum uses the carry from bit 0.
    check_bit1_sum: assert property (
        @(posedge clk) S[1] == (A[1] ^ B[1] ^ fa_carry(A[0], B[0], Ci))
    );

    // Bit 2 sum uses the carry from bit 1.
    check_bit2_sum: assert property (
        @(posedge clk) S[2] == (A[2] ^ B[2] ^ fa_carry(A[1], B[1], fa_carry(A[0], B[0], Ci)))
    );

    // Bit 3 sum uses the carry from bit 2.
    check_bit3_sum: assert property (
        @(posedge clk) S[3] == (A[3] ^ B[3] ^ fa_carry(A[2], B[2], fa_carry(A[1], B[1], fa_carry(A[0], B[0], Ci))))
    );

    // Carry-out matches the final full-adder carry.
    check_final_carry: assert property (
        @(posedge clk) Co == fa_carry(A[3], B[3], fa_carry(A[2], B[2], fa_carry(A[1], B[1], fa_carry(A[0], B[0], Ci))))
    );

    // With no carry-in, the outputs equal plain 4-bit addition.
    check_no_carry_in_addition: assert property (
        @(posedge clk) (!Ci) |-> ({Co, S} == ({1'b0, A} + {1'b0, B}))
    );

    // With A at zero, only B and Ci contribute to the result.
    check_zero_a_addition: assert property (
        @(posedge clk) (A == 4'b0000) |-> ({Co, S} == ({1'b0, B} + {4'b0000, Ci}))
    );

    // With B at zero, only A and Ci contribute to the result.
    check_zero_b_addition: assert property (
        @(posedge clk) (B == 4'b0000) |-> ({Co, S} == ({1'b0, A} + {4'b0000, Ci}))
    );

    // With both operands at zero, the result equals the carry-in.
    check_carry_in_only: assert property (
        @(posedge clk) ((A == 4'b0000) && (B == 4'b0000)) |-> ({Co, S} == {4'b0000, Ci})
    );

endmodule