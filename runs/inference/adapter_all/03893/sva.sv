module ripple_carry_adder_sva (
    input logic CLK,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] SUM
);
    // SUM equals 4-bit A + B (truncated to 4 bits).
    check_sum_matches_add: assert property (
        @(posedge CLK) SUM == (A + B)[3:0]
    );

    // LSB sum equals A[0] ^ B[0] (CARRY_IN=0).
    check_sum_bit0: assert property (
        @(posedge CLK) SUM[0] == (A[0] ^ B[0])
    );

    // Bit1 sum equals A[1] ^ B[1] ^ (A[0] & B[0]).
    check_sum_bit1: assert property (
        @(posedge CLK) SUM[1] == (A[1] ^ B[1] ^ (A[0] & B[0]))
    );

    // Bit2 sum equals A[2] ^ B[2] ^ ((A[1]&B[1]) | ((A[0]&B[0]) & (A[1]^B[1]))).
    check_sum_bit2: assert property (
        @(posedge CLK) SUM[2] == (A[2] ^ B[2] ^ ((A[1]&B[1]) | ((A[0]&B[0]) & (A[1]^B[1]))))
    );

    // Bit3 sum equals A[3] ^ B[3] ^ ((A[2]&B[2]) | ((A[1]&B[1]) & (A[2]^B[2])) | ((A[0]&B[0]) & (A[1]^B[1]) & (A[2]^B[2]))).
    check_sum_bit3: assert property (
        @(posedge CLK) SUM[3] == (A[3] ^ B[3] ^ ((A[2]&B[2]) | ((A[1]&B[1]) & (A[2]^B[2])) | ((A[0]&B[0]) & (A[1]^B[1]) & (A[2]^B[2]))))
    );

    // If inputs are stable, output remains stable (purely combinational behavior).
    check_stability_when_inputs_stable: assert property (
        @(posedge CLK) $stable(A) && $stable(B) |-> $stable(SUM)
    );

    // If A is zero, SUM equals B (truncation).
    check_zero_A_identity: assert property (
        @(posedge CLK) (A == 4'b0000) |-> (SUM == B)
    );

    // If B is zero, SUM equals A (truncation).
    check_zero_B_identity: assert property (
        @(posedge CLK) (B == 4'b0000) |-> (SUM == A)
    );

    // If A equals B, SUM is zero (truncation).
    check_equal_inputs_zero_sum: assert property (
        @(posedge CLK) (A == B) |-> (SUM == 4'b0000)
    );

    // If A is all ones, SUM equals bitwise NOT of B (truncation).
    check_all_ones_A_inverts_B: assert property (
        @(posedge CLK) (A == 4'hF) |-> (SUM == ~B)
    );

    // If B is all ones, SUM equals bitwise NOT of A (truncation).
    check_all_ones_B_inverts_A: assert property (
        @(posedge CLK) (B == 4'hF) |-> (SUM == ~A)
    );
endmodule