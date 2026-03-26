module adder_4bit_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] S,
    input logic C_out
);

    // Full 5-bit result matches A plus B.
    check_total_sum: assert property (
        @(posedge clk) ({C_out, S} == ({1'b0, A} + {1'b0, B}))
    );

    // Bit 0 sum is XOR with zero carry-in.
    check_bit0_sum: assert property (
        @(posedge clk) (S[0] == (A[0] ^ B[0]))
    );

    // Bit 1 sum includes the carry from bit 0.
    check_bit1_sum: assert property (
        @(posedge clk) (S[1] == (A[1] ^ B[1] ^ (({1'b0, A[0]} + {1'b0, B[0]})[1])))
    );

    // Bit 2 sum includes the carry from the lower two bits.
    check_bit2_sum: assert property (
        @(posedge clk) (S[2] == (A[2] ^ B[2] ^ (({1'b0, A[1:0]} + {1'b0, B[1:0]})[2])))
    );

    // Bit 3 sum includes the carry from the lower three bits.
    check_bit3_sum: assert property (
        @(posedge clk) (S[3] == (A[3] ^ B[3] ^ (({1'b0, A[2:0]} + {1'b0, B[2:0]})[3])))
    );

    // Carry-out is the MSB of the full unsigned addition.
    check_carry_out: assert property (
        @(posedge clk) (C_out == (({1'b0, A} + {1'b0, B})[4]))
    );

endmodule