module sky130_fd_sc_lp__o31ai_sva (
    input logic clk,
    input logic Y,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1
);

    // Y matches the implemented OR-then-NAND function.
    check_output_function: assert property (
        @(posedge clk) Y == ~((A1 | A2 | A3) & B1)
    );

    // A low B1 forces the NAND output high.
    check_b1_low_forces_y_high: assert property (
        @(posedge clk) (B1 == 1'b0) |-> (Y == 1'b1)
    );

    // All A inputs low force the OR term low and Y high.
    check_all_a_low_forces_y_high: assert property (
        @(posedge clk) ((A1 == 1'b0) && (A2 == 1'b0) && (A3 == 1'b0)) |-> (Y == 1'b1)
    );

    // A high B1 with any A input high forces Y low.
    check_active_inputs_force_y_low: assert property (
        @(posedge clk) ((B1 == 1'b1) && ((A1 == 1'b1) || (A2 == 1'b1) || (A3 == 1'b1))) |-> (Y == 1'b0)
    );

    // A low Y requires B1 to be high and at least one A input high.
    check_y_low_has_valid_cause: assert property (
        @(posedge clk) (Y == 1'b0) |-> ((B1 == 1'b1) && ((A1 == 1'b1) || (A2 == 1'b1) || (A3 == 1'b1)))
    );

    // A high Y requires B1 to be low or all A inputs low.
    check_y_high_has_valid_cause: assert property (
        @(posedge clk) (Y == 1'b1) |-> ((B1 == 1'b0) || ((A1 == 1'b0) && (A2 == 1'b0) && (A3 == 1'b0)))
    );

endmodule