module binary_adder_sva(
    input logic       clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       CTRL,
    input logic [3:0] C
);

    // When CTRL is low, C is the 4-bit sum of A and B.
    check_add_mode_sum: assert property (
        @(posedge clk) (CTRL == 1'b0) |-> (C == (A + B))
    );

    // When CTRL is high, C is the sum of zero-extended A[3:1] and B[3:1].
    check_shift_mode_sum: assert property (
        @(posedge clk) (CTRL == 1'b1) |-> (C == ({1'b0, A[3:1]} + {1'b0, B[3:1]}))
    );

    // In add mode, a zero B operand leaves A unchanged.
    check_add_mode_b_zero_identity: assert property (
        @(posedge clk) ((CTRL == 1'b0) && (B == 4'b0000)) |-> (C == A)
    );

    // In add mode, a zero A operand leaves B unchanged.
    check_add_mode_a_zero_identity: assert property (
        @(posedge clk) ((CTRL == 1'b0) && (A == 4'b0000)) |-> (C == B)
    );

    // In add mode, overflow wraps to 4 bits on C.
    check_add_mode_overflow_wrap: assert property (
        @(posedge clk) ((CTRL == 1'b0) && (A == 4'hF) && (B == 4'h1)) |-> (C == 4'h0)
    );

    // In shifted mode, zero upper bits on B leave zero-extended A[3:1].
    check_shift_mode_b_upper_zero_identity: assert property (
        @(posedge clk) ((CTRL == 1'b1) && (B[3:1] == 3'b000)) |-> (C == {1'b0, A[3:1]})
    );

    // In shifted mode, zero upper bits on A leave zero-extended B[3:1].
    check_shift_mode_a_upper_zero_identity: assert property (
        @(posedge clk) ((CTRL == 1'b1) && (A[3:1] == 3'b000)) |-> (C == {1'b0, B[3:1]})
    );

    // In shifted mode, the LSB of C is the sum bit from A[1] and B[1].
    check_shift_mode_lsb: assert property (
        @(posedge clk) (CTRL == 1'b1) |-> (C[0] == (A[1] ^ B[1]))
    );

    // In shifted mode, zero upper slices on both operands force C to zero.
    check_shift_mode_upper_zero_gives_zero: assert property (
        @(posedge clk) ((CTRL == 1'b1) && (A[3:1] == 3'b000) && (B[3:1] == 3'b000)) |-> (C == 4'b0000)
    );

    // In shifted mode, carry from the selected upper bits propagates into C[3].
    check_shift_mode_carry_example: assert property (
        @(posedge clk) ((CTRL == 1'b1) && (A[3:1] == 3'b111) && (B[3:1] == 3'b001)) |-> (C == 4'b1000)
    );

endmodule