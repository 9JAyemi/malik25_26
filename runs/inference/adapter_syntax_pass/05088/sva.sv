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

    // SUM matches A ^ B ^ ~CIN.
    check_sum_function: assert property (
        @(posedge clk) SUM == (A ^ B ^ ~CIN)
    );

    // COUT matches the OR of the three AND terms.
    check_cout_function: assert property (
        @(posedge clk) COUT == ((A & B) | (A & ~CIN) | (B & ~CIN))
    );

    // With CIN low, SUM is A ^ B.
    check_sum_when_cin_low: assert property (
        @(posedge clk) (CIN == 1'b0) |-> (SUM == (A ^ B))
    );

    // With CIN high, SUM is A | B.
    check_sum_when_cin_high: assert property (
        @(posedge clk) (CIN == 1'b1) |-> (SUM == (A | B))
    );

    // With CIN low, COUT is A & B.
    check_cout_when_cin_low: assert property (
        @(posedge clk) (CIN == 1'b0) |-> (COUT == (A & B))
    );

    // With CIN high, COUT is A | B.
    check_cout_when_cin_high: assert property (
        @(posedge clk) (CIN == 1'b1) |-> (COUT == (A | B))
    );

    // When A and B are equal, SUM follows ~CIN.
    check_sum_when_ab_equal: assert property (
        @(posedge clk) (A == B) |-> (SUM == ~CIN)
    );

    // When A and B differ, SUM follows CIN.
    check_sum_when_ab_different: assert property (
        @(posedge clk) (A != B) |-> (SUM == CIN)
    );

    // When A and B are equal, COUT follows A.
    check_cout_when_ab_equal: assert property (
        @(posedge clk) (A == B) |-> (COUT == A)
    );

    // When A and B differ, COUT follows ~CIN.
    check_cout_when_ab_different: assert property (
        @(posedge clk) (A != B) |-> (COUT == ~CIN)
    );

endmodule