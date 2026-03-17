module logic_circuit_sva (
    input logic clk,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic X
);

    // X equals the AND of the two OR terms.
    check_x_matches_logic_function: assert property (
        @(posedge clk) X == ((A1 | A2) & (B1 | B2))
    );

    // If both A inputs are low, X must be low.
    check_no_a_input_forces_x_low: assert property (
        @(posedge clk) !(A1 | A2) |-> (X == 1'b0)
    );

    // If both B inputs are low, X must be low.
    check_no_b_input_forces_x_low: assert property (
        @(posedge clk) !(B1 | B2) |-> (X == 1'b0)
    );

    // If both OR terms are high, X must be high.
    check_both_or_terms_drive_x_high: assert property (
        @(posedge clk) ((A1 | A2) & (B1 | B2)) |-> (X == 1'b1)
    );

    // X can only be high when both OR terms are high.
    check_x_high_requires_both_or_terms: assert property (
        @(posedge clk) (X == 1'b1) |-> ((A1 | A2) & (B1 | B2))
    );

endmodule