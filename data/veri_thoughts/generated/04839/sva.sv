module sky130_fd_sc_ms__o2bb2a_sva (
    input logic clk,
    input logic X,
    input logic A1_N,
    input logic A2_N,
    input logic B1,
    input logic B2
);

    // X matches the implemented NAND-OR-AND function.
    check_output_matches_logic: assert property (
        @(posedge clk)
        X === ((~(A2_N & A1_N)) & (B2 | B1))
    );

    // If both B inputs are low, the OR leg forces X low.
    check_or_leg_low_forces_x_low: assert property (
        @(posedge clk)
        ((B1 === 1'b0) && (B2 === 1'b0)) |-> (X === 1'b0)
    );

    // If both A inputs are high, the NAND leg forces X low.
    check_nand_leg_low_forces_x_low: assert property (
        @(posedge clk)
        ((A1_N === 1'b1) && (A2_N === 1'b1)) |-> (X === 1'b0)
    );

    // X is high when the OR leg is high and at least one A input is low.
    check_both_legs_enable_x_high: assert property (
        @(posedge clk)
        (((B1 === 1'b1) || (B2 === 1'b1)) &&
         ((A1_N === 1'b0) || (A2_N === 1'b0))) |-> (X === 1'b1)
    );

    // A high X requires both the OR leg and NAND leg to be active.
    check_x_high_has_valid_causes: assert property (
        @(posedge clk)
        (X === 1'b1) |-> (((B1 === 1'b1) || (B2 === 1'b1)) &&
                          ((A1_N === 1'b0) || (A2_N === 1'b0)))
    );

endmodule