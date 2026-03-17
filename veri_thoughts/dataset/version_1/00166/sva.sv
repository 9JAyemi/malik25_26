module sky130_fd_sc_hdll__o21ai_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1
);

    // Y must implement the OR-AND-invert function.
    check_function_equation: assert property (
        @(posedge clk) Y == ~((A1 | A2) & B1)
    );

    // A low B1 forces the NAND output high.
    check_b1_low_forces_y_high: assert property (
        @(posedge clk) (B1 == 1'b0) |-> (Y == 1'b1)
    );

    // If both OR inputs are low, Y must be high.
    check_a_inputs_low_force_y_high: assert property (
        @(posedge clk) ((A1 == 1'b0) && (A2 == 1'b0)) |-> (Y == 1'b1)
    );

    // A1 high with B1 high forces Y low.
    check_a1_and_b1_force_y_low: assert property (
        @(posedge clk) ((A1 == 1'b1) && (B1 == 1'b1)) |-> (Y == 1'b0)
    );

    // A2 high with B1 high forces Y low.
    check_a2_and_b1_force_y_low: assert property (
        @(posedge clk) ((A2 == 1'b1) && (B1 == 1'b1)) |-> (Y == 1'b0)
    );

    // Y can be low only when B1 is high.
    check_y_low_requires_b1_high: assert property (
        @(posedge clk) (Y == 1'b0) |-> (B1 == 1'b1)
    );

    // Y can be low only when at least one OR input is high.
    check_y_low_requires_or_input_high: assert property (
        @(posedge clk) (Y == 1'b0) |-> ((A1 == 1'b1) || (A2 == 1'b1))
    );

    // With B1 high, a high Y requires both OR inputs low.
    check_y_high_with_b1_high_requires_a_inputs_low: assert property (
        @(posedge clk) ((Y == 1'b1) && (B1 == 1'b1)) |-> ((A1 == 1'b0) && (A2 == 1'b0))
    );

endmodule