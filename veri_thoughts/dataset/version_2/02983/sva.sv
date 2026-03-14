module adder_sva (
    input logic CLK,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] S,
    input logic C_out
);
    // Helper expressions for ripple-carry chain.
    let c0_expr = (A[0] & B[0]);
    let c1_expr = (A[1] & B[1]) | (A[1] & c0_expr) | (B[1] & c0_expr);
    let c2_expr = (A[2] & B[2]) | (A[2] & c1_expr) | (B[2] & c1_expr);

    ///// Functional correctness /////
    // Overall 5-bit sum matches zero-extended addition of A and B.
    check_total_sum: assert property (
        @(posedge CLK) {C_out, S} == ({1'b0, A} + {1'b0, B})
    );

    // LSB sum has no carry-in.
    check_s0: assert property (
        @(posedge CLK) S[0] == (A[0] ^ B[0])
    );

    // Bit1 sum uses carry from bit0 = A0&B0.
    check_s1: assert property (
        @(posedge CLK) S[1] == (A[1] ^ B[1] ^ c0_expr)
    );

    // Bit2 sum uses carry from bit1.
    check_s2: assert property (
        @(posedge CLK) S[2] == (A[2] ^ B[2] ^ c1_expr)
    );

    // Bit3 sum uses carry from bit2.
    check_s3: assert property (
        @(posedge CLK) S[3] == (A[3] ^ B[3] ^ c2_expr)
    );

    // Carry-out equals generate/propagate of bit3 with carry2.
    check_cout: assert property (
        @(posedge CLK) C_out == ((A[3] & B[3]) | (A[3] & c2_expr) | (B[3] & c2_expr))
    );

    ///// Basic identities /////
    // Adding zero (B==0) returns A with no carry.
    check_add_zero_B: assert property (
        @(posedge CLK) (B == 4'b0000) |-> ((S == A) && (C_out == 1'b0))
    );

    // Adding zero (A==0) returns B with no carry.
    check_add_zero_A: assert property (
        @(posedge CLK) (A == 4'b0000) |-> ((S == B) && (C_out == 1'b0))
    );

    // 0 + 0 yields 0 with no carry.
    check_zero_plus_zero: assert property (
        @(posedge CLK) ((A == 4'b0000) && (B == 4'b0000)) |-> ((S == 4'b0000) && (C_out == 1'b0))
    );

    ///// Stability /////
    // If inputs are stable cycle-to-cycle, outputs are stable.
    check_functional_stability: assert property (
        @(posedge CLK) $stable(A) && $stable(B) |-> $stable(S) && $stable(C_out)
    );

    ///// Overflow relation /////
    // Carry-out implies 5-bit arithmetic sum exceeds 0x0F.
    check_cout_implies_overflow: assert property (
        @(posedge CLK) (C_out == 1'b1) |-> (({1'b0, A} + {1'b0, B}) >= 5'd16)
    );

endmodule