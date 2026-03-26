module mux_nand_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic sel1,
    input logic sel2,
    input logic Y
);

    // RTL is combinational with no reset; assertions are sampled on clk.

    // Y must match the implemented combinational equation.
    check_output_equation: assert property (
        @(posedge clk)
        Y == ~((~sel1 & A) | (~sel2 & B) | (~sel1 & ~sel2 & C))
    );

    // When both selects are high, all terms are disabled and Y is high.
    check_both_selects_high: assert property (
        @(posedge clk)
        (sel1 && sel2) |-> (Y == 1'b1)
    );

    // When only the A term is enabled, Y is the inverse of A.
    check_a_term_only_mode: assert property (
        @(posedge clk)
        (!sel1 && sel2) |-> (Y == ~A)
    );

    // When only the B term is enabled, Y is the inverse of B.
    check_b_term_only_mode: assert property (
        @(posedge clk)
        (sel1 && !sel2) |-> (Y == ~B)
    );

    // When all terms are enabled, Y is the NAND of A, B, and C.
    check_all_terms_enabled_mode: assert property (
        @(posedge clk)
        (!sel1 && !sel2) |-> (Y == ~(A | B | C))
    );

    // A high with sel1 low forces the output low.
    check_a_forces_low: assert property (
        @(posedge clk)
        (!sel1 && A) |-> (Y == 1'b0)
    );

    // B high with sel2 low forces the output low.
    check_b_forces_low: assert property (
        @(posedge clk)
        (!sel2 && B) |-> (Y == 1'b0)
    );

    // C high with both selects low forces the output low.
    check_c_forces_low: assert property (
        @(posedge clk)
        (!sel1 && !sel2 && C) |-> (Y == 1'b0)
    );

    // A low output must come from at least one active product term.
    check_low_output_has_active_term: assert property (
        @(posedge clk)
        (Y == 1'b0) |-> ((!sel1 && A) || (!sel2 && B) || (!sel1 && !sel2 && C))
    );

    // A high output means none of the implemented product terms is active.
    check_high_output_has_no_active_term: assert property (
        @(posedge clk)
        (Y == 1'b1) |-> ((sel1 || !A) && (sel2 || !B) && (sel1 || sel2 || !C))
    );

endmodule