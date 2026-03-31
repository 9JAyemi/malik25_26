module sky130_fd_sc_ms__o31ai_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1
);

    // Y matches the NAND of B1 and the OR of A1/A2/A3.
    check_function_equivalence: assert property (
        @(posedge clk) Y == ~(B1 & (A1 | A2 | A3))
    );

    // B1 low forces the NAND output high.
    check_b1_low_forces_y_high: assert property (
        @(posedge clk) !B1 |-> Y
    );

    // All A inputs low force the OR term low and Y high.
    check_all_a_low_forces_y_high: assert property (
        @(posedge clk) !(A1 | A2 | A3) |-> Y
    );

    // B1 high with any A input high forces Y low.
    check_active_inputs_force_y_low: assert property (
        @(posedge clk) (B1 & (A1 | A2 | A3)) |-> !Y
    );

    // A low Y requires B1 high and at least one A input high.
    check_y_low_requires_active_inputs: assert property (
        @(posedge clk) !Y |-> (B1 & (A1 | A2 | A3))
    );

    // A high Y requires B1 low or all A inputs low.
    check_y_high_requires_inactive_inputs: assert property (
        @(posedge clk) Y |-> (!B1 | !(A1 | A2 | A3))
    );

endmodule