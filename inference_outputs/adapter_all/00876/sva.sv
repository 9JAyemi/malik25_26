module three_to_one_sva (
    input logic clk,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic Y
);

    // Y must match the implemented OR-of-products function.
    check_y_matches_function: assert property (
        @(posedge clk) Y == ((A1 & A2) | B1)
    );

    // B1 high must force Y high.
    check_b1_forces_y_high: assert property (
        @(posedge clk) B1 |-> Y
    );

    // A1 and A2 high together must force Y high.
    check_a1_a2_force_y_high: assert property (
        @(posedge clk) (A1 & A2) |-> Y
    );

    // With B1 low, Y reduces to the A1&A2 term.
    check_b1_low_reduces_to_and_term: assert property (
        @(posedge clk) !B1 |-> (Y == (A1 & A2))
    );

    // With A1&A2 low, Y reduces to B1.
    check_and_term_low_reduces_to_b1: assert property (
        @(posedge clk) !(A1 & A2) |-> (Y == B1)
    );

    // If both OR inputs are low, Y must be low.
    check_both_inputs_low_force_y_low: assert property (
        @(posedge clk) (!B1 && !(A1 & A2)) |-> !Y
    );

    // Y high must come from B1 or the A1&A2 term.
    check_y_high_has_valid_source: assert property (
        @(posedge clk) Y |-> (B1 || (A1 & A2))
    );

endmodule