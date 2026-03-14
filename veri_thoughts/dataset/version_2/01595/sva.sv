module magnitude_comparator_sva (
    input logic clk,
    input logic [2:0] A,
    input logic [2:0] B,
    input logic a_greater,
    input logic b_greater,
    input logic equal
);
    // a_greater reflects (A > B).
    check_a_greater_definition: assert property (
        @(posedge clk) a_greater == (A > B)
    );

    // b_greater reflects (B > A).
    check_b_greater_definition: assert property (
        @(posedge clk) b_greater == (B > A)
    );

    // equal reflects (A == B).
    check_equal_definition: assert property (
        @(posedge clk) equal == (A == B)
    );

    // Exactly one of a_greater, b_greater, equal is HIGH.
    check_outputs_onehot: assert property (
        @(posedge clk) $onehot({a_greater, b_greater, equal})
    );

    // equal excludes both greater outputs.
    check_equal_excludes_greater: assert property (
        @(posedge clk) equal |-> (!a_greater && !b_greater)
    );

    // a_greater excludes b_greater and equal.
    check_a_greater_excludes_others: assert property (
        @(posedge clk) a_greater |-> (!b_greater && !equal)
    );

    // b_greater excludes a_greater and equal.
    check_b_greater_excludes_others: assert property (
        @(posedge clk) b_greater |-> (!a_greater && !equal)
    );

    // (a_greater || b_greater) matches (A != B).
    check_neq_matches_any_greater: assert property (
        @(posedge clk) (a_greater || b_greater) == (A != B)
    );

    // equal matches NOT (a_greater || b_greater).
    check_eq_matches_not_any_greater: assert property (
        @(posedge clk) equal == !(a_greater || b_greater)
    );
endmodule