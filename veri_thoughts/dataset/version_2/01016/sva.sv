module bitwise_and_sva (
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [7:0] C
);
    ///// Functional correctness /////
    // C equals the bitwise AND of A and B.
    check_output_is_and: assert property (
        @($global_clock) C == (A & B)
    );

    // C cannot have 1s where A has 0s.
    check_c_subset_of_a: assert property (
        @($global_clock) (C & ~A) == 8'h00
    );

    // C cannot have 1s where B has 0s.
    check_c_subset_of_b: assert property (
        @($global_clock) (C & ~B) == 8'h00
    );

    // If A is all zeros, C must be all zeros.
    check_zero_when_a_zero: assert property (
        @($global_clock) (A == 8'h00) |-> (C == 8'h00)
    );

    // If B is all zeros, C must be all zeros.
    check_zero_when_b_zero: assert property (
        @($global_clock) (B == 8'h00) |-> (C == 8'h00)
    );

    // If A is all ones, C equals B.
    check_pass_b_when_a_all_ones: assert property (
        @($global_clock) (A == 8'hFF) |-> (C == B)
    );

    // If B is all ones, C equals A.
    check_pass_a_when_b_all_ones: assert property (
        @($global_clock) (B == 8'hFF) |-> (C == A)
    );

    // If A equals B, C equals A (idempotence).
    check_when_a_equals_b: assert property (
        @($global_clock) (A == B) |-> (C == A)
    );

    // No spurious 1s in C where either A or B has 0.
    check_no_spurious_one_bits: assert property (
        @($global_clock) (C & ((~A) | (~B))) == 8'h00
    );
endmodule