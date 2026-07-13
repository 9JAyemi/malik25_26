module ripple_carry_adder_sva (
    input  logic        clk,   // sampling clock (RTL has no clock/reset)
    input  logic [3:0]  A,
    input  logic [3:0]  B,
    input  logic        CI,
    input  logic [3:0]  S,
    input  logic        CO,
    input  logic [3:0]  C      // internal carry chain
);
    // Final 5-bit result equals A+B+CI.
    check_full_sum: assert property (
        @(posedge clk) disable iff (1'b0) {CO, S} == ({1'b0, A} + {1'b0, B} + CI)
    );

    // S[0] equals A[0]^B[0]^CI.
    check_sum0_xor: assert property (
        @(posedge clk) disable iff (1'b0) S[0] == (A[0] ^ B[0] ^ CI)
    );
    // S[1] equals A[1]^B[1]^C[0].
    check_sum1_xor: assert property (
        @(posedge clk) disable iff (1'b0) S[1] == (A[1] ^ B[1] ^ C[0])
    );
    // S[2] equals A[2]^B[2]^C[1].
    check_sum2_xor: assert property (
        @(posedge clk) disable iff (1'b0) S[2] == (A[2] ^ B[2] ^ C[1])
    );
    // S[3] equals A[3]^B[3]^C[2].
    check_sum3_xor: assert property (
        @(posedge clk) disable iff (1'b0) S[3] == (A[3] ^ B[3] ^ C[2])
    );

    // C[0] equals majority(A[0],B[0],CI).
    check_carry0_majority: assert property (
        @(posedge clk) disable iff (1'b0) C[0] == ((A[0] & B[0]) | (B[0] & CI) | (A[0] & CI))
    );
    // C[1] equals majority(A[1],B[1],C[0]).
    check_carry1_majority: assert property (
        @(posedge clk) disable iff (1'b0) C[1] == ((A[1] & B[1]) | (B[1] & C[0]) | (A[1] & C[0]))
    );
    // C[2] equals majority(A[2],B[2],C[1]).
    check_carry2_majority: assert property (
        @(posedge clk) disable iff (1'b0) C[2] == ((A[2] & B[2]) | (B[2] & C[1]) | (A[2] & C[1]))
    );
    // CO equals majority(A[3],B[3],C[2]).
    check_carry3_majority: assert property (
        @(posedge clk) disable iff (1'b0) CO == ((A[3] & B[3]) | (B[3] & C[2]) | (A[3] & C[2]))
    );
endmodule