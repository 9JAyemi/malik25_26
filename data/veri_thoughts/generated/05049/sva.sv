module adder4_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] S,
    input logic C,
    input logic clk
);

    // Sum and carry must match A+B.
    check_total_sum: assert property (
        @(posedge clk) {C, S} == ({1'b0, A} + {1'b0, B})
    );

    // Bit 0 is the XOR of the LSB inputs.
    check_lsb_sum: assert property (
        @(posedge clk) S[0] == (A[0] ^ B[0])
    );

    // Bit 1 includes the carry from bit 0.
    check_bit1_sum: assert property (
        @(posedge clk) S[1] == (A[1] ^ B[1] ^ (A[0] & B[0]))
    );

    // Bit 2 includes the carry from the lower two bits.
    check_bit2_sum: assert property (
        @(posedge clk) S[2] == (A[2] ^ B[2] ^ (({1'b0, A[1:0]} + {1'b0, B[1:0]})[2]))
    );

    // Bit 3 includes the carry from the lower three bits.
    check_bit3_sum: assert property (
        @(posedge clk) S[3] == (A[3] ^ B[3] ^ (({1'b0, A[2:0]} + {1'b0, B[2:0]})[3]))
    );

    // C is the carry-out of the 4-bit addition.
    check_carry_out: assert property (
        @(posedge clk) C == (({1'b0, A} + {1'b0, B})[4])
    );

    // Zero on A passes B through.
    check_zero_a_identity: assert property (
        @(posedge clk) (A == 4'b0000) |-> (S == B && C == 1'b0)
    );

    // Zero on B passes A through.
    check_zero_b_identity: assert property (
        @(posedge clk) (B == 4'b0000) |-> (S == A && C == 1'b0)
    );

    // Stable inputs keep outputs stable.
    check_stable_inputs_stable_outputs: assert property (
        @(posedge clk) ($stable(A) && $stable(B)) |-> ($stable(S) && $stable(C))
    );

endmodule