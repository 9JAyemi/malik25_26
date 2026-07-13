module sky130_fd_sc_hd__o221ai_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1
);

// Y matches the implemented NAND/OR/NAND/BUF function.
    check_functional_equivalence: assert property (
        @(posedge clk) Y == ~((A1 | A2) & (B1 | B2) & C1)
    );

// C1 low forces Y high.
    check_c1_low_forces_y_high: assert property (
        @(posedge clk) !C1 |-> Y
    );

// With C1 high, both A and B OR terms low force Y high.
    check_ab_terms_low_force_y_high: assert property (
        @(posedge clk) C1 && !(A1 || A2) && !(B1 || B2) |-> Y
    );

// With C1 high, A1 high with B terms low forces Y high.
    check_a1_with_b_terms_low_force_y_high: assert property (
        @(posedge clk) C1 && A1 && !(B1 || B2) |-> Y
    );

// With C1 high, A2 high with B terms low forces Y high.
    check_a2_with_b_terms_low_force_y_high: assert property (
        @(posedge clk) C1 && A2 && !(B1 || B2) |-> Y
    );

// With C1 high, B1 high with A terms low forces Y high.
    check_b1_with_a_terms_low_force_y_high: assert property (
        @(posedge clk) C1 && B1 && !(A1 || A2) |-> Y
    );

// With C1 high, B2 high with A terms low forces Y high.
    check_b2_with_a_terms_low_force_y_high: assert property (
        @(posedge clk) C1 && B2 && !(A1 || A2) |-> Y
    );

// With C1 high, any asserted A and B OR term forces Y low.
    check_any_ab_term_with_c1_high_forces_y_low: assert property (
        @(posedge clk) C1 && ((A1 || A2) && (B1 || B2)) |-> !Y
    );

// With C1 high, Y low implies at least one asserted A and B OR term.
    check_y_low_implies_ab_terms_high_with_c1_high: assert property (
        @(posedge clk) C1 && !Y |-> ((A1 || A2) && (B1 || B2))
    );

// With C1 high, Y high implies all A and B OR terms are low.
    check_y_high_implies_ab_terms_low_with_c1_high: assert property (
        @(posedge clk) C1 && Y |-> !(A1 || A2) || !(B1 || B2)
    );

endmodule
