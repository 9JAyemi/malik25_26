module sky130_fd_sc_ms__o31ai_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1
);

    // Y matches the implemented OR-then-NAND function.
    check_output_function: assert property (
        @(posedge clk) Y == ~(B1 & (A1 | A2 | A3))
    );

    // A low B1 forces the NAND output high.
    check_b1_low_forces_y_high: assert property (
        @(posedge clk) !B1 |-> Y
    );

    // All A inputs low force the OR term low and Y high.
    check_all_a_low_forces_y_high: assert property (
        @(posedge clk) (!A1 && !A2 && !A3) |-> Y
    );

    // A high B1 with any A input high forces Y low.
    check_active_inputs_force_y_low: assert property (
        @(posedge clk) (B1 && (A1 || A2 || A3)) |-> !Y
    );

    // A low Y requires B1 to be high and at least one A input high.
    check_y_low_has_valid_cause: assert property (
        @(posedge clk) !Y |-> (B1 && (A1 || A2 || A3))
    );

endmodule