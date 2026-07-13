module ripple_carry_adder_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic CI,
    input logic [3:0] S,
    input logic CO
);
    // Functional correctness: 5-bit sum equals A+B+CI.
    check_sum_matches_addition: assert property (
        @(posedge $global_clock) {CO, S} == ({1'b0, A} + {1'b0, B} + CI)
    );

    // Carry-out equals MSB of the 5-bit sum.
    check_carry_msb_of_sum: assert property (
        @(posedge $global_clock) CO == (({1'b0, A} + {1'b0, B} + CI)[4])
    );

    // LSB sum bit equals XOR of A[0], B[0], and CI.
    check_lsb_xor: assert property (
        @(posedge $global_clock) S[0] == (A[0] ^ B[0] ^ CI)
    );

    // When B==0 and CI==0, output is A (no carry).
    check_passthrough_a_when_b_zero_ci_zero: assert property (
        @(posedge $global_clock) (B == 4'd0 && CI == 1'b0) |-> ({CO, S} == {1'b0, A})
    );

    // When B==0 and CI==1, output is A+1 (with possible carry).
    check_increment_a_when_b_zero_ci_one: assert property (
        @(posedge $global_clock) (B == 4'd0 && CI == 1'b1) |-> ({CO, S} == ({1'b0, A} + 5'd1))
    );

    // When A==0 and CI==0, output is B (no carry).
    check_passthrough_b_when_a_zero_ci_zero: assert property (
        @(posedge $global_clock) (A == 4'd0 && CI == 1'b0) |-> ({CO, S} == {1'b0, B})
    );

    // When A==0 and CI==1, output is B+1 (with possible carry).
    check_increment_b_when_a_zero_ci_one: assert property (
        @(posedge $global_clock) (A == 4'd0 && CI == 1'b1) |-> ({CO, S} == ({1'b0, B} + 5'd1))
    );

    // Max case: A=15, B=15, CI=1 -> result is 31 (all ones).
    check_all_ones_with_cin_one_full_scale: assert property (
        @(posedge $global_clock) (A == 4'hF && B == 4'hF && CI == 1'b1) |-> ({CO, S} == 5'b1_1111)
    );

    // All zeros with CI=0 -> result is zero.
    check_zero_zero_zero: assert property (
        @(posedge $global_clock) (A == 4'd0 && B == 4'd0 && CI == 1'b0) |-> ({CO, S} == 5'd0)
    );

    // Commutativity: swapping A and B does not change the result.
    check_commutativity: assert property (
        @(posedge $global_clock) {CO, S} == ({1'b0, B} + {1'b0, A} + CI)
    );
endmodule