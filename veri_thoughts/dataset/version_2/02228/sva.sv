module my_module_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic E,
    input logic F,
    input logic G,
    input logic H,
    input logic I,
    input logic J,
    input logic X
);
    // X equals ((A&B&C&D) || (E&F&G&H) || (I&J)).
    check_x_equals_expr: assert property (
        @(posedge clk) disable iff (1'b0) X == ((A && B && C && D) || (E && F && G && H) || (I && J))
    );

    // If A&B&C&D are all 1, X must be 1.
    check_x_one_if_abcd: assert property (
        @(posedge clk) disable iff (1'b0) (A && B && C && D) |-> (X == 1'b1)
    );

    // If E&F&G&H are all 1, X must be 1.
    check_x_one_if_efgh: assert property (
        @(posedge clk) disable iff (1'b0) (E && F && G && H) |-> (X == 1'b1)
    );

    // If I&J are both 1, X must be 1.
    check_x_one_if_ij: assert property (
        @(posedge clk) disable iff (1'b0) (I && J) |-> (X == 1'b1)
    );

    // If none of the enabling terms are true, X must be 0.
    check_x_zero_if_no_terms: assert property (
        @(posedge clk) disable iff (1'b0) !((A && B && C && D) || (E && F && G && H) || (I && J)) |-> (X == 1'b0)
    );

    // If X is 1, at least one enabling term must be true.
    check_x_one_implies_some_term: assert property (
        @(posedge clk) disable iff (1'b0) (X == 1'b1) |-> ((A && B && C && D) || (E && F && G && H) || (I && J))
    );
endmodule