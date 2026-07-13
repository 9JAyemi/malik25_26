module adder_subtractor_sva (
    input logic        clk,
    input logic [3:0]  A,
    input logic [3:0]  B,
    input logic        C,
    input logic [3:0]  Y
);

    // With C low, no carry path is active and Y is A XOR B.
    check_xor_mode: assert property (
        @(posedge clk) (!C) |-> (Y == (A ^ B))
    );

    // With B at zero, all output bits pass through A.
    check_zero_b_passthrough: assert property (
        @(posedge clk) (B == 4'b0000) |-> (Y == A)
    );

    // Bit 0 follows the implemented XOR and carry-out equation.
    check_bit0_equation: assert property (
        @(posedge clk) Y[0] == (A[0] ^ B[0] ^ (C & B[0]))
    );

    // Bit 1 uses a carry term only when C is high and A[0] is low.
    check_bit1_equation: assert property (
        @(posedge clk) Y[1] == (A[1] ^ B[1] ^ (C & (~A[0]) & B[1]))
    );

    // Bit 2 uses a carry term only when C is high and A[1:0] are low.
    check_bit2_equation: assert property (
        @(posedge clk) Y[2] == (A[2] ^ B[2] ^ (C & (~A[1]) & (~A[0]) & B[2]))
    );

    // Bit 3 uses a carry term only when C is high and A[2:0] are low.
    check_bit3_equation: assert property (
        @(posedge clk) Y[3] == (A[3] ^ B[3] ^ (C & (~A[2]) & (~A[1]) & (~A[0]) & B[3]))
    );

    // When C is high, bit 0 always collapses to A[0].
    check_c_mode_bit0_passthrough: assert property (
        @(posedge clk) C |-> (Y[0] == A[0])
    );

    // When C is high and A[0] is low, bit 1 collapses to A[1].
    check_c_mode_bit1_passthrough: assert property (
        @(posedge clk) (C && (A[0] == 1'b0)) |-> (Y[1] == A[1])
    );

    // When C is high and A[1:0] are low, bit 2 collapses to A[2].
    check_c_mode_bit2_passthrough: assert property (
        @(posedge clk) (C && (A[1:0] == 2'b00)) |-> (Y[2] == A[2])
    );

    // When C is high and A[2:0] are low, bit 3 collapses to A[3].
    check_c_mode_bit3_passthrough: assert property (
        @(posedge clk) (C && (A[2:0] == 3'b000)) |-> (Y[3] == A[3])
    );

endmodule