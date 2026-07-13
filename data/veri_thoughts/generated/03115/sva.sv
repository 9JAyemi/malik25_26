module sky130_fd_sc_ms__a2111o_assertions (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1,
    input logic D1
);

    // X matches the implemented OR-of-four function.
    check_exact_function: assert property (
        @(posedge clk) X == (C1 || B1 || D1 || (A1 && A2))
    );

    // Any asserted direct OR input forces X high.
    check_direct_or_inputs_drive_high: assert property (
        @(posedge clk) (C1 || B1 || D1) |-> X
    );

    // The A1/A2 product term forces X high.
    check_and_term_drives_high: assert property (
        @(posedge clk) (A1 && A2) |-> X
    );

    // If all contributing terms are low, X must be low.
    check_all_terms_low_drive_low: assert property (
        @(posedge clk) (!C1 && !B1 && !D1 && (!A1 || !A2)) |-> !X
    );

    // A low X means no input term is asserting the OR.
    check_low_output_implies_low_terms: assert property (
        @(posedge clk) !X |-> (!C1 && !B1 && !D1 && (!A1 || !A2))
    );

    // With direct OR inputs low, a high X must come from A1&A2.
    check_high_output_requires_and_term_without_direct_or: assert property (
        @(posedge clk) (X && !C1 && !B1 && !D1) |-> (A1 && A2)
    );

    // Stable sampled inputs imply a stable sampled output.
    check_sampled_stability: assert property (
        @(posedge clk) $stable({A1, A2, B1, C1, D1}) |-> $stable(X)
    );

endmodule