module o311ai_sva (
    input logic clk,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic C1,
    input logic Y
);

    // Y must match the implemented combinational logic.
    check_y_matches_logic: assert property (
        @(posedge clk) Y == ((A2 | (A1 & B1)) & (~A3) & C1)
    );

    // A3 high forces Y low through the inverted A3 term.
    check_a3_masks_output: assert property (
        @(posedge clk) (A3 == 1'b1) |-> (Y == 1'b0)
    );

    // C1 low forces Y low through the final AND gate.
    check_c1_masks_output: assert property (
        @(posedge clk) (C1 == 1'b0) |-> (Y == 1'b0)
    );

    // A2 high drives Y high when the gating terms are enabled.
    check_a2_drives_output_when_enabled: assert property (
        @(posedge clk) ((A2 == 1'b1) && (A3 == 1'b0) && (C1 == 1'b1)) |-> (Y == 1'b1)
    );

    // A1 and B1 high together drive Y high when the gating terms are enabled.
    check_a1b1_drives_output_when_enabled: assert property (
        @(posedge clk) ((A1 == 1'b1) && (B1 == 1'b1) && (A3 == 1'b0) && (C1 == 1'b1)) |-> (Y == 1'b1)
    );

    // With no OR-path active and the gates enabled, Y must be low.
    check_no_or_term_keeps_output_low: assert property (
        @(posedge clk) ((A2 == 1'b0) && !((A1 == 1'b1) && (B1 == 1'b1)) && (A3 == 1'b0) && (C1 == 1'b1)) |-> (Y == 1'b0)
    );

    // A high Y requires C1 high, A3 low, and at least one OR input path true.
    check_y_high_has_valid_causes: assert property (
        @(posedge clk) (Y == 1'b1) |-> ((C1 == 1'b1) && (A3 == 1'b0) && ((A2 == 1'b1) || ((A1 == 1'b1) && (B1 == 1'b1))))
    );

endmodule