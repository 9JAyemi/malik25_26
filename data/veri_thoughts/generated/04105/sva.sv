module sky130_fd_sc_ls__o2111ai_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1,
    input logic D1
);

    // Y must match the buffered NAND of B1, C1, D1, and (A1 | A2).
    check_y_matches_comb_logic: assert property (
        @(posedge clk) Y == ~((A1 | A2) & B1 & C1 & D1)
    );

    // If both A inputs are low, the OR term is low and Y must be high.
    check_or_term_low_forces_y_high: assert property (
        @(posedge clk) (!A1 && !A2) |-> (Y == 1'b1)
    );

    // If B1 is low, one NAND input is low and Y must be high.
    check_b1_low_forces_y_high: assert property (
        @(posedge clk) (!B1) |-> (Y == 1'b1)
    );

    // If C1 is low, one NAND input is low and Y must be high.
    check_c1_low_forces_y_high: assert property (
        @(posedge clk) (!C1) |-> (Y == 1'b1)
    );

    // If D1 is low, one NAND input is low and Y must be high.
    check_d1_low_forces_y_high: assert property (
        @(posedge clk) (!D1) |-> (Y == 1'b1)
    );

    // If all effective NAND inputs are high, Y must be low.
    check_all_terms_high_force_y_low: assert property (
        @(posedge clk) ((A1 | A2) & B1 & C1 & D1) |-> (Y == 1'b0)
    );

    // A low Y requires every effective NAND input to be high.
    check_y_low_requires_all_terms_high: assert property (
        @(posedge clk) (Y == 1'b0) |-> ((A1 | A2) & B1 & C1 & D1)
    );

endmodule