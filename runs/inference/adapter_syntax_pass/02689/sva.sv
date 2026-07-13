module bitwise_operators_sva #(
    parameter n = 4
) (
    input logic [n-1:0] A,
    input logic [n-1:0] B,
    input logic [n-1:0] and_res,
    input logic [n-1:0] or_res,
    input logic [n-1:0] xor_res,
    input logic [n-1:0] not_res
);

    // and_res must equal A AND B.
    check_and_result: assert property (
        @($global_clock) and_res == (A & B)
    );

    // or_res must equal A OR B.
    check_or_result: assert property (
        @($global_clock) or_res == (A | B)
    );

    // xor_res must equal A XOR B.
    check_xor_result: assert property (
        @($global_clock) xor_res == (A ^ B)
    );

    // not_res must equal bitwise NOT of A.
    check_not_result: assert property (
        @($global_clock) not_res == (~A)
    );

    // and_res must be a subset of A.
    check_and_subset_a: assert property (
        @($global_clock) (and_res & ~A) == {n{1'b0}}
    );

    // and_res must be a subset of B.
    check_and_subset_b: assert property (
        @($global_clock) (and_res & ~B) == {n{1'b0}}
    );

    // or_res must contain all bits set in A.
    check_or_superset_a: assert property (
        @($global_clock) ((or_res & ~A) == {n{1'b0}})
    );

    // or_res must contain all bits set in B.
    check_or_superset_b: assert property (
        @($global_clock) ((or_res & ~B) == {n{1'b0}})
    );

    // xor_res must be disjoint from and_res.
    check_xor_disjoint_and: assert property (
        @($global_clock) ((xor_res & and_res) == {n{1'b0}})
    );

    // xor_res must equal A XOR (A AND B).
    check_xor_decomposition: assert property (
        @($global_clock) xor_res == (A ^ (A & B))
    );

endmodule