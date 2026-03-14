module ripple_carry_adder_sva (
    input logic        clk,
    input logic [3:0]  A,
    input logic [3:0]  B,
    input logic        C_in,
    input logic [3:0]  S,
    input logic        C_out
);
    // 3-input majority function
    function automatic logic maj3 (input logic x, input logic y, input logic z);
        maj3 = (x & y) | (x & z) | (y & z);
    endfunction

    ///// Functional correctness of registered outputs /////
    // S equals previous-cycle A+B+C_in (low 4 bits).
    check_sum_matches_prev_inputs: assert property (
        @(posedge clk) S == (($past(A) + $past(B) + $past(C_in)) & 4'hF)
    );

    // C_out equals previous-cycle majority of A[3], B[3], and C_in.
    check_cout_matches_prev_inputs: assert property (
        @(posedge clk) C_out == maj3($past(A[3]), $past(B[3]), $past(C_in))
    );

    ///// Bit-level sum correctness /////
    // Bit 0 is XOR of previous-cycle A[0], B[0], and C_in.
    check_s0_xor: assert property (
        @(posedge clk) S[0] == ($past(A[0]) ^ $past(B[0]) ^ $past(C_in))
    );

    // Bit 1 is XOR of A[1], B[1], and carry from bit 0 (all from previous cycle).
    check_s1_xor_with_c1: assert property (
        @(posedge clk) S[1] == ($past(A[1]) ^ $past(B[1]) ^ maj3($past(A[0]), $past(B[0]), $past(C_in)))
    );

    // Bit 2 is XOR of A[2], B[2], and carry from bit 1 (prev cycle).
    check_s2_xor_with_c2: assert property (
        @(posedge clk) S[2] == ($past(A[2]) ^ $past(B[2]) ^ maj3($past(A[1]), $past(B[1]), maj3($past(A[0]), $past(B[0]), $past(C_in))))
    );

    // Bit 3 is XOR of A[3], B[3], and carry from bit 2 (prev cycle).
    check_s3_xor_with_c3: assert property (
        @(posedge clk) S[3] == ($past(A[3]) ^ $past(B[3]) ^ maj3($past(A[2]), $past(B[2]), maj3($past(A[1]), $past(B[1]), maj3($past(A[0]), $past(B[0]), $past(C_in)))))
    );

    ///// Carry-out corner cases derived from implemented logic /////
    // If previous-cycle A[3]=0 and B[3]=0, C_out must be 0.
    check_cout_zero_when_msbs_zero: assert property (
        @(posedge clk) ($past(A[3]) == 1'b0 && $past(B[3]) == 1'b0) |-> (C_out == 1'b0)
    );

    // If previous-cycle A[3]=1 and B[3]=1, C_out must be 1.
    check_cout_one_when_msbs_one: assert property (
        @(posedge clk) ($past(A[3]) == 1'b1 && $past(B[3]) == 1'b1) |-> (C_out == 1'b1)
    );

    // If previous-cycle A[3] != B[3], C_out equals previous-cycle C_in.
    check_cout_equals_cin_when_msbs_differ: assert property (
        @(posedge clk) ($past(A[3]) ^ $past(B[3])) |-> (C_out == $past(C_in))
    );

    ///// Simple identity cases for the sum /////
    // When previous-cycle B==0 and C_in==0, S equals previous-cycle A.
    check_sum_identity_B_zero: assert property (
        @(posedge clk) ($past(B) == 4'b0000 && $past(C_in) == 1'b0) |-> (S == $past(A))
    );

    // When previous-cycle A==0 and C_in==0, S equals previous-cycle B.
    check_sum_identity_A_zero: assert property (
        @(posedge clk) ($past(A) == 4'b0000 && $past(C_in) == 1'b0) |-> (S == $past(B))
    );

    // When previous-cycle B==0 and C_in==1, S equals previous-cycle A+1 (mod 16).
    check_sum_increment_B_zero_Cin1: assert property (
        @(posedge clk) ($past(B) == 4'b0000 && $past(C_in) == 1'b1) |-> (S == (($past(A) + 4'd1) & 4'hF))
    );

endmodule