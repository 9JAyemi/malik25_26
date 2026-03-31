module sky130_fd_sc_ms__o21ai_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // Y matches the implemented OR-then-NAND function.
    check_output_function: assert property (
        @($global_clock) Y == ~((A1 | A2) & B1)
    );

    // A low B1 forces the NAND output high.
    check_b1_low_forces_y_high: assert property (
        @($global_clock) (B1 == 1'b0) |-> (Y == 1'b1)
    );

    // Both A inputs low force the OR term low and Y high.
    check_a_inputs_low_force_y_high: assert property (
        @($global_clock) ((A1 == 1'b0) && (A2 == 1'b0)) |-> (Y == 1'b1)
    );

    // A high B1 and a high OR term force Y low.
    check_active_inputs_force_y_low: assert property (
        @($global_clock) ((B1 == 1'b1) && ((A1 == 1'b1) || (A2 == 1'b1))) |-> (Y == 1'b0)
    );

    // A low Y requires B1 to be high and the OR term to be high.
    check_y_low_has_valid_cause: assert property (
        @($global_clock) (Y == 1'b0) |-> ((B1 == 1'b1) && ((A1 == 1'b1) || (A2 == 1'b1)))
    );

    // A high Y requires B1 to be low or the OR term to be low.
    check_y_high_has_valid_cause: assert property (
        @($global_clock) (Y == 1'b1) |-> ((B1 == 1'b0) || ((A1 == 1'b0) && (A2 == 1'b0)))
    );

endmodule