module comparator_2bit_sva (
    input logic clk,
    input logic [1:0] A,
    input logic [1:0] B,
    input logic [1:0] C
);

    ///// C[1] behavior /////
    // C[1] equals (A[1] & ~B[1]) per (A[1] > B[1]).
    check_c1_definition: assert property (
        @(posedge clk) C[1] == (A[1] & ~B[1])
    );

    // When MSBs are equal, C[1] must be 0.
    check_c1_zero_when_msbs_equal: assert property (
        @(posedge clk) (A[1] == B[1]) |-> (C[1] == 1'b0)
    );

    // When MSBs differ, C[1] equals A[1].
    check_c1_matches_a1_on_mismatch: assert property (
        @(posedge clk) (A[1] != B[1]) |-> (C[1] == A[1])
    );

    ///// C[0] behavior /////
    // When MSBs are equal, C[0] equals (A[0] >= B[0]).
    check_c0_when_msbs_equal: assert property (
        @(posedge clk) (A[1] == B[1]) |-> (C[0] == (A[0] >= B[0]))
    );

    // When MSBs differ, C[0] equals ~C[1].
    check_c0_complement_when_msbs_differ: assert property (
        @(posedge clk) (A[1] != B[1]) |-> (C[0] == ~C[1])
    );

    ///// Output coding /////
    // Output is never 2'b11.
    check_c_never_11: assert property (
        @(posedge clk) (C != 2'b11)
    );

    // If A[1]=1 and B[1]=0, output must be 2'b10.
    check_case_msbs_10: assert property (
        @(posedge clk) (A[1] && !B[1]) |-> (C == 2'b10)
    );

    // If A[1]=0 and B[1]=1, output must be 2'b01.
    check_case_msbs_01: assert property (
        @(posedge clk) (!A[1] && B[1]) |-> (C == 2'b01)
    );

    // If A[1]=0 and B[1]=0, C = {1'b0, (A[0] >= B[0])}.
    check_case_msbs_00: assert property (
        @(posedge clk) (!A[1] && !B[1]) |-> (C == {1'b0, (A[0] >= B[0])})
    );

    // If A[1]=1 and B[1]=1, C = {1'b0, (A[0] >= B[0])}.
    check_case_msbs_11: assert property (
        @(posedge clk) (A[1] && B[1]) |-> (C == {1'b0, (A[0] >= B[0])})
    );

    ///// Temporal sanity /////
    // Any rise of C[1] implies A[1]=1 and B[1]=0 at that time.
    check_c1_rise_condition: assert property (
        @(posedge clk) $rose(C[1]) |-> (A[1] && !B[1])
    );

endmodule