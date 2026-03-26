module majority_gate_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic X
);

    // X matches the RTL assign expression.
    check_output_matches_rtl_function: assert property (
        @(posedge clk)
        X == ((((A & B) | (A & C) | (A & D) | (B & C) | (B & D) | (C & D)) &
              ~((~(A & B)) & (~(A & C)) & (~(A & D)) & (~(B & C)) & (~(B & D)) & (~(C & D))))
    );

    // The AB term alone is sufficient to drive X high.
    check_ab_term_sets_x: assert property (
        @(posedge clk)
        (A & B) |-> (X == 1'b1)
    );

    // The AC term alone is sufficient to drive X high.
    check_ac_term_sets_x: assert property (
        @(posedge clk)
        (A & C) |-> (X == 1'b1)
    );

    // The AD term alone is sufficient to drive X high.
    check_ad_term_sets_x: assert property (
        @(posedge clk)
        (A & D) |-> (X == 1'b1)
    );

    // The BC term alone is sufficient to drive X high.
    check_bc_term_sets_x: assert property (
        @(posedge clk)
        (B & C) |-> (X == 1'b1)
    );

    // The BD term alone is sufficient to drive X high.
    check_bd_term_sets_x: assert property (
        @(posedge clk)
        (B & D) |-> (X == 1'b1)
    );

    // The CD term alone is sufficient to drive X high.
    check_cd_term_sets_x: assert property (
        @(posedge clk)
        (C & D) |-> (X == 1'b1)
    );

    // If no pairwise AND term is high, X must be low.
    check_no_pair_high_clears_x: assert property (
        @(posedge clk)
        ~((A & B) | (A & C) | (A & D) | (B & C) | (B & D) | (C & D)) |-> (X == 1'b0)
    );

endmodule