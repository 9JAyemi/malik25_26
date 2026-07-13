module sky130_fd_sc_lp__o31ai_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1
);

    // Y matches the OR-NAND-buffer logic function.
    check_y_matches_o31ai_function: assert property (
        @(posedge clk) Y == ~(B1 & (A1 | A2 | A3))
    );

    // A low B1 forces the NAND output high.
    check_b1_low_forces_y_high: assert property (
        @(posedge clk) !B1 |-> Y
    );

    // With all A inputs low, the OR term is low and Y is high.
    check_all_a_low_forces_y_high: assert property (
        @(posedge clk) (!A1 && !A2 && !A3) |-> Y
    );

    // B1 high and any asserted A input forces Y low.
    check_b1_and_any_a_high_forces_y_low: assert property (
        @(posedge clk) (B1 && (A1 || A2 || A3)) |-> !Y
    );

    // The A1 path participates in driving Y low when B1 is high.
    check_a1_with_b1_forces_y_low: assert property (
        @(posedge clk) (B1 && A1) |-> !Y
    );

    // The A2 path participates in driving Y low when B1 is high.
    check_a2_with_b1_forces_y_low: assert property (
        @(posedge clk) (B1 && A2) |-> !Y
    );

    // The A3 path participates in driving Y low when B1 is high.
    check_a3_with_b1_forces_y_low: assert property (
        @(posedge clk) (B1 && A3) |-> !Y
    );

    // A low Y requires B1 high and the OR term high.
    check_y_low_requires_active_nand_inputs: assert property (
        @(posedge clk) !Y |-> (B1 && (A1 || A2 || A3))
    );

    // If B1 is high and Y is high, the OR term must be low.
    check_y_high_with_b1_requires_or_term_low: assert property (
        @(posedge clk) (B1 && Y) |-> (!A1 && !A2 && !A3)
    );

endmodule