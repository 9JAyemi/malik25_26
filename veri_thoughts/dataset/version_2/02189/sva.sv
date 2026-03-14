module binary_adder_sva (
    input  logic        clk,
    input  logic [3:0]  A,
    input  logic [3:0]  B,
    input  logic [3:0]  sum,
    input  logic        C_out
);

    // Sum and carry-out must match 5-bit addition of A and B.
    check_full_sum: assert property (
        @(posedge clk) {C_out, sum} == ({1'b0, A} + {1'b0, B})
    );

    // Carry-out equals the overflow bit of the 5-bit addition.
    check_cout_overflow_bit: assert property (
        @(posedge clk) C_out == ({1'b0, A} + {1'b0, B})[4]
    );

    // Sum equals the low 4 bits of the 5-bit addition.
    check_sum_low4: assert property (
        @(posedge clk) sum == ({1'b0, A} + {1'b0, B})[3:0]
    );

    // LSB sum bit equals A[0] XOR B[0].
    check_sum_bit0: assert property (
        @(posedge clk) sum[0] == (A[0] ^ B[0])
    );

    // sum[1] equals A[1] XOR B[1] XOR carry from bit0 (A[0]&B[0]).
    check_sum_bit1: assert property (
        @(posedge clk) sum[1] == ((A[1] ^ B[1]) ^ (A[0] & B[0]))
    );

    // sum[2] equals A[2] XOR B[2] XOR carry from bit1.
    check_sum_bit2: assert property (
        @(posedge clk)
            sum[2] ==
            ((A[2] ^ B[2]) ^
             ((A[1] & B[1]) | ((A[1] ^ B[1]) & (A[0] & B[0]))))
    );

    // sum[3] equals A[3] XOR B[3] XOR carry from bit2.
    check_sum_bit3: assert property (
        @(posedge clk)
            sum[3] ==
            ((A[3] ^ B[3]) ^
             ((A[2] & B[2]) |
              ((A[2] ^ B[2]) & (A[1] & B[1])) |
              ((A[2] ^ B[2]) & (A[1] ^ B[1]) & (A[0] & B[0]))))
    );

    // Carry-out equals ripple-carry expression using generate/propagate.
    check_cout_formula: assert property (
        @(posedge clk)
            C_out ==
            ((A[3] & B[3]) |
             ((A[3] ^ B[3]) & (A[2] & B[2])) |
             ((A[3] ^ B[3]) & (A[2] ^ B[2]) & (A[1] & B[1])) |
             ((A[3] ^ B[3]) & (A[2] ^ B[2]) & (A[1] ^ B[1]) & (A[0] & B[0])))
    );

    // Adding zero on B leaves sum = A and C_out = 0.
    check_add_zero_B: assert property (
        @(posedge clk) (B == 4'b0000) |-> (sum == A) && (C_out == 1'b0)
    );

    // Adding zero on A leaves sum = B and C_out = 0.
    check_add_zero_A: assert property (
        @(posedge clk) (A == 4'b0000) |-> (sum == B) && (C_out == 1'b0)
    );

    // If both MSBs are 0, carry-out must be 0.
    check_no_carry_when_msb00: assert property (
        @(posedge clk) (!A[3] && !B[3]) |-> (C_out == 1'b0)
    );

    // If both MSBs are 1, carry-out must be 1.
    check_carry_when_msb11: assert property (
        @(posedge clk) (A[3] && B[3]) |-> (C_out == 1'b1)
    );

endmodule