module sky130_fd_sc_ms__o211ai_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1
);

    // Y matches the implemented OR-NAND-BUF function.
    check_function_equivalence: assert property (
        @(posedge clk) Y == ~((A1 | A2) & B1 & C1)
    );

    // B1 low forces the NAND output high.
    check_b1_low_forces_y_high: assert property (
        @(posedge clk) !B1 |-> Y
    );

    // C1 low forces the NAND output high.
    check_c1_low_forces_y_high: assert property (
        @(posedge clk) !C1 |-> Y
    );

    // Both A inputs low force the OR term low and Y high.
    check_a_inputs_low_force_y_high: assert property (
        @(posedge clk) (!A1 && !A2) |-> Y
    );

    // B1 and C1 high with either A input high force Y low.
    check_active_inputs_force_y_low: assert property (
        @(posedge clk) (B1 && C1 && (A1 || A2)) |-> !Y
    );

    // A low Y requires B1 and C1 high and the OR term high.
    check_y_low_requires_active_inputs: assert property (
        @(posedge clk) !Y |-> (B1 && C1 && (A1 || A2))
    );

    // A high Y requires at least one NAND input low.
    check_y_high_requires_inactive_nand_input: assert property (
        @(posedge clk) Y |-> (!B1 || !C1 || (!A1 && !A2))
    );

endmodule