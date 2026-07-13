module full_adder_sva (
    input logic CLK,
    input logic A,
    input logic B,
    input logic CI,
    input logic SUM,
    input logic COUT
);

// SUM equals A ^ B ^ CI.
    check_sum_function: assert property (
        @(posedge CLK) SUM == (A ^ B ^ CI)
    );

// COUT equals (A & B) | (B & CI) | (CI & A).
    check_cout_function: assert property (
        @(posedge CLK) COUT == ((A & B) | (B & CI) | (CI & A))
    );

// When A and B are equal, SUM equals CI.
    check_sum_when_ab_equal: assert property (
        @(posedge CLK) (A == B) |-> (SUM == CI)
    );

// When A and B are equal, COUT equals CI.
    check_cout_when_ab_equal: assert property (
        @(posedge CLK) (A == B) |-> (COUT == CI)
    );

// When A and B differ, SUM equals ~CI.
    check_sum_when_ab_differs: assert property (
        @(posedge CLK) (A != B) |-> (SUM == ~CI)
    );

// When A and B differ, COUT equals CI.
    check_cout_when_ab_differs: assert property (
        @(posedge CLK) (A != B) |-> (COUT == CI)
    );

// When CI is 0, SUM equals A ^ B.
    check_sum_when_ci_zero: assert property (
        @(posedge CLK) (CI == 1'b0) |-> (SUM == (A ^ B))
    );

// When CI is 0, COUT equals A & B.
    check_cout_when_ci_zero: assert property (
        @(posedge CLK) (CI == 1'b0) |-> (COUT == (A & B))
    );

// When CI is 1, SUM equals ~(A ^ B).
    check_sum_when_ci_one: assert property (
        @(posedge CLK) (CI == 1'b1) |-> (SUM == ~(A ^ B))
    );

// When CI is 1, COUT equals A | B.
    check_cout_when_ci_one: assert property (
        @(posedge CLK) (CI == 1'b1) |-> (COUT == (A | B))
    );

endmodule
