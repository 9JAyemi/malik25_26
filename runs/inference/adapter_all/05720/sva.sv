module my_module_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1
);

    // X must match the implemented OR-of-terms function.
    check_x_matches_or_function: assert property (
        @(posedge clk) X == (A1 & A2) | B1 | C1
    );

    // B1 high must force X high.
    check_b1_forces_x_high: assert property (
        @(posedge clk) B1 |-> X
    );

    // C1 high must force X high.
    check_c1_forces_x_high: assert property (
        @(posedge clk) C1 |-> X
    );

    // A1 and A2 high together must force X high.
    check_a1_a2_force_x_high: assert property (
        @(posedge clk) (A1 & A2) |-> X
    );

    // With B1 and C1 low, X reduces to the A1&A2 term.
    check_no_b1_c1_reduces_to_and_term: assert property (
        @(posedge clk) (!B1 && !C1) |-> (X == (A1 & A2))
    );

    // With A1 and A2 low, X reduces to the OR of B1 and C1.
    check_no_a1_a2_reduces_to_b1_or_c1: assert property (
        @(posedge clk) (!A1 && !A2) |-> (X == (B1 | C1))
    );

    // If X is low, both B1 and C1 must be low and not both A1 and A2 can be high.
    check_x_low_requires_no_b1_c1_and_not_both_a1_a2: assert property (
        @(posedge clk) !X |-> (!B1 && !C1 && !(A1 && A2))
    );

    // If X is high, at least one OR input term must be true.
    check_x_high_requires_some_input_term: assert property (
        @(posedge clk) X |-> (B1 || C1 || (A1 && A2))
    );

endmodule