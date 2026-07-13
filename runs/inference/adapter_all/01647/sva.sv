module bitwise_and_sva (
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [7:0] C
);
    // C equals bitwise AND of A and B.
    check_and_function: assert property (
        @(posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3] or posedge A[4] or negedge A[4] or posedge A[5] or negedge A[5] or posedge A[6] or negedge A[6] or posedge A[7] or negedge A[7] or posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1] or posedge B[2] or negedge B[2] or posedge B[3] or negedge B[3] or posedge B[4] or negedge B[4] or posedge B[5] or negedge B[5] or posedge B[6] or negedge B[6] or posedge B[7] or negedge B[7])
        C == (A & B)
    );

    // If C is 0, both A and B must be 0.
    check_zero_implies_inputs_zero: assert property (
        @(posedge C[0] or negedge C[0] or posedge C[1] or negedge C[1] or posedge C[2] or negedge C[2] or posedge C[3] or negedge C[3] or posedge C[4] or negedge C[4] or posedge C[5] or negedge C[5] or posedge C[6] or negedge C[6] or posedge C[7] or negedge C[7])
        (C == 8'h00) |-> ((A == 8'h00) && (B == 8'h00))
    );

    // If A is 0, C must be 0.
    check_a_zero_implies_c_zero: assert property (
        @(posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3] or posedge A[4] or negedge A[4] or posedge A[5] or negedge A[5] or posedge A[6] or negedge A[6] or posedge A[7] or negedge A[7])
        (A == 8'h00) |-> (C == 8'h00)
    );

    // If B is 0, C must be 0.
    check_b_zero_implies_c_zero: assert property (
        @(posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1] or posedge B[2] or negedge B[2] or posedge B[3] or negedge B[3] or posedge B[4] or negedge B[4] or posedge B[5] or negedge B[5] or posedge B[6] or negedge B[6] or posedge B[7] or negedge B[7])
        (B == 8'h00) |-> (C == 8'h00)
    );

    // If A is all 1s, C equals B.
    check_a_all_ones_passthrough: assert property (
        @(posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3] or posedge A[4] or negedge A[4] or posedge A[5] or negedge A[5] or posedge A[6] or negedge A[6] or posedge A[7] or negedge A[7])
        (A == 8'hFF) |-> (C == B)
    );

    // If B is all 1s, C equals A.
    check_b_all_ones_passthrough: assert property (
        @(posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1] or posedge B[2] or negedge B[2] or posedge B[3] or negedge B[3] or posedge B[4] or negedge B[4] or posedge B[5] or negedge B[5] or posedge B[6] or negedge B[6] or posedge B[7] or negedge B[7])
        (B == 8'hFF) |-> (C == A)
    );

    // If A is all 0s, C must be 0.
    check_a_all_zeros_implies_c_zero: assert property (
        @(posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3] or posedge A[4] or negedge A[4] or posedge A[5] or negedge A[5] or posedge A[6] or negedge A[6] or posedge A[7] or negedge A[7])
        (A == 8'h00) |-> (C == 8'h00)
    );

    // If B is all 0s, C must be 0.
    check_b_all_zeros_implies_c_zero: assert property (
        @(posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1] or posedge B[2] or negedge B[2] or posedge B[3] or negedge B[3] or posedge B[4] or negedge B[4] or posedge B[5] or negedge B[5] or posedge B[6] or negedge B[6] or posedge B[7] or negedge B[7])
        (B == 8'h00) |-> (C == 8'h00)
    );

    // If A is stable, C equals A & B.
    check_stable_a_implies_c_equals_and: assert property (
        @(posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3] or posedge A[4] or negedge A[4] or posedge A[5] or negedge A[5] or posedge A[6] or negedge A[6] or posedge A[7] or negedge A[7])
        $stable(A) |-> (C == (A & B))
    );

    // If B is stable, C equals A & B.
    check_stable_b_implies_c_equals_and: assert property (
        @(posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1] or posedge B[2] or negedge B[2] or posedge B[3] or negedge B[3] or posedge B[4] or negedge B[4] or posedge B[5] or negedge B[5] or posedge B[6] or negedge B[6] or posedge B[7] or negedge B[7])
        $stable(B) |-> (C == (A & B))
    );
endmodule