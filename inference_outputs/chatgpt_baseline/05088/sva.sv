module binary_adder_sva (
    input logic clk,
    input logic COUT,
    input logic SUM,
    input logic A,
    input logic B,
    input logic CIN,
    input logic VDD,
    input logic VSS
);

    // SUM implements A XOR B XOR inverted CIN.
    check_sum_equation: assert property (
        @(posedge clk) SUM == (A ^ B ^ ~CIN)
    );

    // COUT implements (A&B) | (A&~CIN) | (B&~CIN).
    check_cout_equation: assert property (
        @(posedge clk) COUT == ((A & B) | (A & ~CIN) | (B & ~CIN))
    );

    // With CIN high, SUM reduces to A XOR B.
    check_sum_when_cin_high: assert property (
        @(posedge clk) CIN |-> (SUM == (A ^ B))
    );

    // With CIN high, COUT reduces to A AND B.
    check_cout_when_cin_high: assert property (
        @(posedge clk) CIN |-> (COUT == (A & B))
    );

    // With CIN low, SUM reduces to XNOR of A and B.
    check_sum_when_cin_low: assert property (
        @(posedge clk) !CIN |-> (SUM == ~(A ^ B))
    );

    // With CIN low, COUT reduces to OR of A and B.
    check_cout_when_cin_low: assert property (
        @(posedge clk) !CIN |-> (COUT == (A | B))
    );

    // When A and B match, SUM equals inverted CIN.
    check_sum_when_a_b_equal: assert property (
        @(posedge clk) (A == B) |-> (SUM == ~CIN)
    );

    // When A and B differ, SUM equals CIN.
    check_sum_when_a_b_differ: assert property (
        @(posedge clk) (A != B) |-> (SUM == CIN)
    );

    // When A and B match, COUT equals A.
    check_cout_when_a_b_equal: assert property (
        @(posedge clk) (A == B) |-> (COUT == A)
    );

    // When A and B differ, COUT equals inverted CIN.
    check_cout_when_a_b_differ: assert property (
        @(posedge clk) (A != B) |-> (COUT == ~CIN)
    );

endmodule