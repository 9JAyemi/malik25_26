module sky130_fd_sc_lp__o211ai_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1
);

    // Y matches the implemented OR-then-NAND function.
    check_y_function: assert property (
        @(posedge clk) Y == ~((A1 | A2) & B1 & C1)
    );

    // Y can be low only when B1, C1, and one A input are high.
    check_y_low_condition: assert property (
        @(posedge clk) (!Y) |-> (B1 & C1 & (A1 | A2))
    );

    // A low B1 input forces the NAND output high.
    check_b1_low_forces_y_high: assert property (
        @(posedge clk) (!B1) |-> Y
    );

    // A low C1 input forces the NAND output high.
    check_c1_low_forces_y_high: assert property (
        @(posedge clk) (!C1) |-> Y
    );

    // Both A inputs low force the OR term low and Y high.
    check_a_inputs_low_force_y_high: assert property (
        @(posedge clk) ((!A1) & (!A2)) |-> Y
    );

    // A1 high with B1 and C1 high drives Y low.
    check_a1_path_drives_y_low: assert property (
        @(posedge clk) (A1 & B1 & C1) |-> (!Y)
    );

    // A2 high with B1 and C1 high drives Y low.
    check_a2_path_drives_y_low: assert property (
        @(posedge clk) (A2 & B1 & C1) |-> (!Y)
    );

endmodule