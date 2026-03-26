module logic_function_sva (
    input logic clk,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1,
    input logic C2,
    input logic X
);

    // X must match the implemented sum-of-products function.
    check_x_matches_logic_function: assert property (
        @(posedge clk)
        X == ((A1 & A2) | (B1 & B2) | (C1 & C2))
    );

    // An asserted A input pair must drive X high.
    check_a_term_sets_x: assert property (
        @(posedge clk)
        (A1 && A2) |-> X
    );

    // An asserted B input pair must drive X high.
    check_b_term_sets_x: assert property (
        @(posedge clk)
        (B1 && B2) |-> X
    );

    // An asserted C input pair must drive X high.
    check_c_term_sets_x: assert property (
        @(posedge clk)
        (C1 && C2) |-> X
    );

    // If no input pair is fully asserted, X must be low.
    check_no_terms_clear_x: assert property (
        @(posedge clk)
        !((A1 && A2) || (B1 && B2) || (C1 && C2)) |-> !X
    );

    // If X is high with B and C terms inactive, the A term must be active.
    check_x_high_with_only_a_path: assert property (
        @(posedge clk)
        X && !(B1 && B2) && !(C1 && C2) |-> (A1 && A2)
    );

    // If X is high with A and C terms inactive, the B term must be active.
    check_x_high_with_only_b_path: assert property (
        @(posedge clk)
        X && !(A1 && A2) && !(C1 && C2) |-> (B1 && B2)
    );

    // If X is high with A and B terms inactive, the C term must be active.
    check_x_high_with_only_c_path: assert property (
        @(posedge clk)
        X && !(A1 && A2) && !(B1 && B2) |-> (C1 && C2)
    );

endmodule