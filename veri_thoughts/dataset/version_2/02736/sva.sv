module four_bit_adder_sva (
    input logic CLK,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] S,
    input logic C
);
    // C matches the RTL equation using A, B, and MSB of (A+B).
    check_c_equation: assert property (
        @(posedge CLK) C == ((A[3] & B[3]) | ((A[3] | B[3]) & ~((A + B)[3])))
    );

    // When no carry, S equals A+B (4-bit).
    check_s_no_carry: assert property (
        @(posedge CLK) (C == 1'b0) |-> (S == (A + B))
    );

    // When carry, S equals (A+B)+1 (4-bit end-around).
    check_s_with_carry: assert property (
        @(posedge CLK) (C == 1'b1) |-> (S == ((A + B) + 1'b1))
    );

    // S equals (A+B)+C (4-bit end-around sum).
    check_s_end_around: assert property (
        @(posedge CLK) S == ((A + B) + C)
    );

    // C equals the carry-out of 5-bit addition {0,A}+{0,B}.
    check_c_as_carryout: assert property (
        @(posedge CLK) C == (({1'b0, A} + {1'b0, B})[4])
    );

    // If both MSBs are 0, carry must be 0.
    check_c_zero_when_msb_zero: assert property (
        @(posedge CLK) ((A[3] == 1'b0) && (B[3] == 1'b0)) |-> (C == 1'b0)
    );

    // If both MSBs are 1, carry must be 1.
    check_c_one_when_msb_one: assert property (
        @(posedge CLK) ((A[3] == 1'b1) && (B[3] == 1'b1)) |-> (C == 1'b1)
    );

    // Carry high implies at least one MSB input is high.
    check_c_implies_any_msb_one: assert property (
        @(posedge CLK) (C == 1'b1) |-> (A[3] | B[3])
    );

    // With differing MSBs and sum[3]==0, carry must be 1.
    check_c_when_msb_diff_and_sum3_zero: assert property (
        @(posedge CLK) ((A[3] ^ B[3]) && (((A + B)[3]) == 1'b0)) |-> (C == 1'b1)
    );

    // With differing MSBs and sum[3]==1, carry must be 0.
    check_c_when_msb_diff_and_sum3_one: assert property (
        @(posedge CLK) ((A[3] ^ B[3]) && (((A + B)[3]) == 1'b1)) |-> (C == 1'b0)
    );
endmodule