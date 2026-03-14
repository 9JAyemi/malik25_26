module sky130_fd_sc_ms__a41o_sva (
    input logic CLK,   // external sampling clock for assertions
    input logic X,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic A4,
    input logic B1
);
    // DUT has no clock/reset; purely combinational: X = (A1&A2&A3&A4) | B1.
    // No reset gating available; using disable iff (1'b0).

    // X equals the specified Boolean function.
    check_function_equation: assert property (
        @(posedge CLK) disable iff (1'b0) X == ((A1 & A2 & A3 & A4) | B1)
    );

    // B1 high forces X high (OR dominance).
    check_B1_forces_X_high: assert property (
        @(posedge CLK) disable iff (1'b0) (B1 == 1'b1) |-> (X == 1'b1)
    );

    // With B1 low, X equals A1&A2&A3&A4.
    check_no_B1_equation: assert property (
        @(posedge CLK) disable iff (1'b0) (B1 == 1'b0) |-> (X == (A1 & A2 & A3 & A4))
    );

    // X high implies either B1 is high or all A inputs are high.
    check_X_high_implies_contributor: assert property (
        @(posedge CLK) disable iff (1'b0) (X == 1'b1) |-> ((B1 == 1'b1) || ((A1 & A2 & A3 & A4) == 1'b1))
    );

    // X low implies B1 is low and not all A inputs are high.
    check_X_low_implies_both_low: assert property (
        @(posedge CLK) disable iff (1'b0) (X == 1'b0) |-> ((B1 == 1'b0) && !((A1 & A2 & A3 & A4) == 1'b1))
    );

    // With B1 low, any single A low forces X low (AND behavior).
    check_A1_zero_blocks_when_B0: assert property (
        @(posedge CLK) disable iff (1'b0) ((B1 == 1'b0) && (A1 == 1'b0)) |-> (X == 1'b0)
    );
    check_A2_zero_blocks_when_B0: assert property (
        @(posedge CLK) disable iff (1'b0) ((B1 == 1'b0) && (A2 == 1'b0)) |-> (X == 1'b0)
    );
    check_A3_zero_blocks_when_B0: assert property (
        @(posedge CLK) disable iff (1'b0) ((B1 == 1'b0) && (A3 == 1'b0)) |-> (X == 1'b0)
    );
    check_A4_zero_blocks_when_B0: assert property (
        @(posedge CLK) disable iff (1'b0) ((B1 == 1'b0) && (A4 == 1'b0)) |-> (X == 1'b0)
    );

    // Rising B1 immediately sets X high.
    check_rose_B1_sets_X: assert property (
        @(posedge CLK) disable iff (1'b0) $rose(B1) |-> (X == 1'b1)
    );

    // Falling B1 makes X equal the AND of A inputs.
    check_fell_B1_sets_X_to_and: assert property (
        @(posedge CLK) disable iff (1'b0) $fell(B1) |-> (X == (A1 & A2 & A3 & A4))
    );

endmodule