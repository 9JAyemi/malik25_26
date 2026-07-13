module compare_module_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] result
);
    // Result matches the RTL function: 0 when A<B, else A^B.
    check_functional_equivalence: assert property (
        @(posedge A[0] or negedge A[0] or
          posedge A[1] or negedge A[1] or
          posedge A[2] or negedge A[2] or
          posedge A[3] or negedge A[3] or
          posedge B[0] or negedge B[0] or
          posedge B[1] or negedge B[1] or
          posedge B[2] or negedge B[2] or
          posedge B[3] or negedge B[3])
        result == ((A < B) ? 4'b0000 : (A ^ B))
    );

    // When A < B, result must be zero.
    check_zero_when_less: assert property (
        @(posedge A[0] or negedge A[0] or
          posedge A[1] or negedge A[1] or
          posedge A[2] or negedge A[2] or
          posedge A[3] or negedge A[3] or
          posedge B[0] or negedge B[0] or
          posedge B[1] or negedge B[1] or
          posedge B[2] or negedge B[2] or
          posedge B[3] or negedge B[3])
        (A < B) |-> (result == 4'b0000)
    );

    // When A >= B, result must equal A ^ B.
    check_xor_when_ge: assert property (
        @(posedge A[0] or negedge A[0] or
          posedge A[1] or negedge A[1] or
          posedge A[2] or negedge A[2] or
          posedge A[3] or negedge A[3] or
          posedge B[0] or negedge B[0] or
          posedge B[1] or negedge B[1] or
          posedge B[2] or negedge B[2] or
          posedge B[3] or negedge B[3])
        !(A < B) |-> (result == (A ^ B))
    );

    // When A == B, result must be zero.
    check_zero_when_equal: assert property (
        @(posedge A[0] or negedge A[0] or
          posedge A[1] or negedge A[1] or
          posedge A[2] or negedge A[2] or
          posedge A[3] or negedge A[3] or
          posedge B[0] or negedge B[0] or
          posedge B[1] or negedge B[1] or
          posedge B[2] or negedge B[2] or
          posedge B[3] or negedge B[3])
        (A == B) |-> (result == 4'b0000)
    );

    // If result is nonzero, A must be greater than B.
    check_nonzero_implies_greater: assert property (
        @(posedge A[0] or negedge A[0] or
          posedge A[1] or negedge A[1] or
          posedge A[2] or negedge A[2] or
          posedge A[3] or negedge A[3] or
          posedge B[0] or negedge B[0] or
          posedge B[1] or negedge B[1] or
          posedge B[2] or negedge B[2] or
          posedge B[3] or negedge B[3])
        (result != 4'b0000) |-> (A > B)
    );

    // If A is greater than B, result must be nonzero.
    check_greater_implies_nonzero: assert property (
        @(posedge A[0] or negedge A[0] or
          posedge A[1] or negedge A[1] or
          posedge A[2] or negedge A[2] or
          posedge A[3] or negedge A[3] or
          posedge B[0] or negedge B[0] or
          posedge B[1] or negedge B[1] or
          posedge B[2] or negedge B[2] or
          posedge B[3] or negedge B[3])
        (A > B) |-> (result != 4'b0000)
    );

    // If result equals A ^ B, then A must be >= B.
    check_result_eq_xor_implies_ge: assert property (
        @(posedge A[0] or negedge A[0] or
          posedge A[1] or negedge A[1] or
          posedge A[2] or negedge A[2] or
          posedge A[3] or negedge A[3] or
          posedge B[0] or negedge B[0] or
          posedge B[1] or negedge B[1] or
          posedge B[2] or negedge B[2] or
          posedge B[3] or negedge B[3])
        (result == (A ^ B)) |-> !(A < B)
    );

    // Result is always either zero or A ^ B.
    check_result_in_expected_set: assert property (
        @(posedge A[0] or negedge A[0] or
          posedge A[1] or negedge A[1] or
          posedge A[2] or negedge A[2] or
          posedge A[3] or negedge A[3] or
          posedge B[0] or negedge B[0] or
          posedge B[1] or negedge B[1] or
          posedge B[2] or negedge B[2] or
          posedge B[3] or negedge B[3])
        (result == 4'b0000) || (result == (A ^ B))
    );
endmodule