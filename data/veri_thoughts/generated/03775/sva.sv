module sky130_fd_sc_hd__xor3_sva (
    input logic clk,
    input logic X,
    input logic A,
    input logic B,
    input logic C
);

    // X must equal the three-input XOR of A, B, and C.
    check_x_matches_xor3: assert property (
        @(posedge clk) X == (A ^ B ^ C)
    );

    // With C low, X reduces to A XOR B.
    check_c_low_reduces_to_ab_xor: assert property (
        @(posedge clk) !C |-> (X == (A ^ B))
    );

    // With C high, X is the inverse of A XOR B.
    check_c_high_inverts_ab_xor: assert property (
        @(posedge clk) C |-> (X == ~(A ^ B))
    );

    // When A and B match, X must equal C.
    check_equal_ab_reduces_to_c: assert property (
        @(posedge clk) (A == B) |-> (X == C)
    );

    // When A and B differ, X must equal the inverse of C.
    check_unequal_ab_inverts_c: assert property (
        @(posedge clk) (A != B) |-> (X == ~C)
    );

    // All-zero inputs must drive X low.
    check_all_zero_drives_zero: assert property (
        @(posedge clk) (!A && !B && !C) |-> !X
    );

    // All-one inputs must drive X high.
    check_all_one_drives_one: assert property (
        @(posedge clk) (A && B && C) |-> X
    );

endmodule