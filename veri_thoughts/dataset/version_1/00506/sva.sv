module sky130_fd_sc_lp__o21a_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1
);

    // X implements (A1 | A2) & B1.
    check_function_equivalence: assert property (
        @(posedge clk) X === ((A1 | A2) & B1)
    );

    // B1 low forces X low.
    check_b1_low_forces_x_low: assert property (
        @(posedge clk) (B1 == 1'b0) |-> (X == 1'b0)
    );

    // Both OR inputs low force X low.
    check_or_inputs_low_force_x_low: assert property (
        @(posedge clk) ((A1 == 1'b0) && (A2 == 1'b0)) |-> (X == 1'b0)
    );

    // A1 high with B1 high drives X high.
    check_a1_and_b1_drive_x_high: assert property (
        @(posedge clk) ((A1 == 1'b1) && (B1 == 1'b1)) |-> (X == 1'b1)
    );

    // A2 high with B1 high drives X high.
    check_a2_and_b1_drive_x_high: assert property (
        @(posedge clk) ((A2 == 1'b1) && (B1 == 1'b1)) |-> (X == 1'b1)
    );

    // X high requires B1 and at least one OR input high.
    check_x_high_requires_valid_inputs: assert property (
        @(posedge clk) (X == 1'b1) |-> ((B1 == 1'b1) && ((A1 == 1'b1) || (A2 == 1'b1)))
    );

endmodule