module logic_gate_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic Y
);
    // No reset in DUT; sample on clk.

    // Y equals (A && !B) || (C && !D).
    check_y_function_equivalence: assert property (
        @(posedge clk) Y == ((A && !B) || (C && !D))
    );

    // If A is 1 and B is 0, Y must be 1.
    check_y_one_when_term1_true: assert property (
        @(posedge clk) (A && !B) |-> (Y == 1'b1)
    );

    // If C is 1 and D is 0, Y must be 1.
    check_y_one_when_term2_true: assert property (
        @(posedge clk) (C && !D) |-> (Y == 1'b1)
    );

    // If B and D are both 1, Y must be 0.
    check_y_zero_when_both_inhibit: assert property (
        @(posedge clk) (B && D) |-> (Y == 1'b0)
    );

    // If A and C are both 0, Y must be 0.
    check_y_zero_when_no_enablers: assert property (
        @(posedge clk) (!A && !C) |-> (Y == 1'b0)
    );

    // Y high implies at least one enabling term is true.
    check_y_high_implies_term_true: assert property (
        @(posedge clk) (Y == 1'b1) |-> ((A && !B) || (C && !D))
    );

    // Y low implies both terms are false.
    check_y_low_implies_terms_false: assert property (
        @(posedge clk) (Y == 1'b0) |-> (!(A && !B) && !(C && !D))
    );
endmodule