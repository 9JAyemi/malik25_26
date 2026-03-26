module four_bit_adder_sva (
    input logic       clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       CI,
    input logic [3:0] C,
    input logic       CO
);

    // Full 5-bit result matches A + B + CI.
    check_total_sum: assert property (
        @(posedge clk) {CO, C} == ({1'b0, A} + {1'b0, B} + CI)
    );

    // Bit 0 matches the RTL full-adder XOR.
    check_bit0_sum: assert property (
        @(posedge clk) C[0] == (A[0] ^ B[0] ^ CI)
    );

    // Bit 1 matches the sum of the lower 2-bit slice plus carry-in.
    check_bit1_sum: assert property (
        @(posedge clk) C[1] == (({1'b0, A[1:0]} + {1'b0, B[1:0]} + CI)[1])
    );

    // Bit 2 matches the sum of the lower 3-bit slice plus carry-in.
    check_bit2_sum: assert property (
        @(posedge clk) C[2] == (({1'b0, A[2:0]} + {1'b0, B[2:0]} + CI)[2])
    );

    // Bit 3 matches the sum of the full 4-bit inputs plus carry-in.
    check_bit3_sum: assert property (
        @(posedge clk) C[3] == (({1'b0, A} + {1'b0, B} + CI)[3])
    );

    // Carry-out matches the overflow bit of the full addition.
    check_carry_out: assert property (
        @(posedge clk) CO == (({1'b0, A} + {1'b0, B} + CI)[4])
    );

endmodule