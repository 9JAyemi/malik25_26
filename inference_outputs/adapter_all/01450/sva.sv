module sky130_fd_sc_ls__o32ai_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic B2
);

    // Y matches the implemented NOR/OR/BUF function.
    check_function_equivalence: assert property (
        @(posedge clk) Y == ~((~(A3 | A1 | A2)) | (~(B1 | B2)))
    );

    // All A inputs high force Y high.
    check_all_a_high_sets_y: assert property (
        @(posedge clk) (A1 && A2 && A3) |-> Y
    );

    // All B inputs high force Y high.
    check_all_b_high_sets_y: assert property (
        @(posedge clk) (B1 && B2) |-> Y
    );

    // With no A inputs high, Y reduces to the B NOR term.
    check_no_a_high_reduces_to_b_nor: assert property (
        @(posedge clk) !(A1 || A2 || A3) |-> (Y == ~(B1 | B2))
    );

    // With no B inputs high, Y reduces to the A NOR term.
    check_no_b_high_reduces_to_a_nor: assert property (
        @(posedge clk) !(B1 || B2) |-> (Y == ~(A3 | A1 | A2))
    );

    // If both NOR terms are low, Y must be high.
    check_both_nor_terms_low_sets_y: assert property (
        @(posedge clk) ((~(A3 | A1 | A2)) && (~(B1 | B2))) |-> Y
    );

    // If Y is low, at least one NOR term must be low.
    check_y_low_requires_one_nor_term_low: assert property (
        @(posedge clk) !Y |-> ((~(A3 | A1 | A2)) || (~(B1 | B2)))
    );

    // If Y is high, both NOR terms must be high.
    check_y_high_requires_both_nor_terms_high: assert property (
        @(posedge clk) Y |-> ((A3 | A1 | A2) && (B1 | B2))
    );

endmodule