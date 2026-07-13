module sky130_fd_sc_lp__xor3_sva (
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

    // If B and C match, X reduces to A.
    check_x_reduces_to_a_when_b_eq_c: assert property (
        @(posedge clk) (B == C) |-> (X == A)
    );

    // If A and C match, X reduces to B.
    check_x_reduces_to_b_when_a_eq_c: assert property (
        @(posedge clk) (A == C) |-> (X == B)
    );

    // If A and B match, X reduces to C.
    check_x_reduces_to_c_when_a_eq_b: assert property (
        @(posedge clk) (A == B) |-> (X == C)
    );

    // Exactly one high input produces a high output.
    check_x_high_for_one_hot_inputs: assert property (
        @(posedge clk)
        ((A && !B && !C) || (!A && B && !C) || (!A && !B && C)) |-> X
    );

    // Exactly two high inputs produce a low output.
    check_x_low_for_two_hot_inputs: assert property (
        @(posedge clk)
        ((A && B && !C) || (A && !B && C) || (!A && B && C)) |-> !X
    );

    // All-low inputs produce a low output.
    check_x_low_for_all_zero: assert property (
        @(posedge clk) (!A && !B && !C) |-> !X
    );

    // All-high inputs produce a high output.
    check_x_high_for_all_one: assert property (
        @(posedge clk) (A && B && C) |-> X
    );

endmodule