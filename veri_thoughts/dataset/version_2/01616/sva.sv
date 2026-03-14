module sky130_fd_sc_hd__a21oi_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic and0_out,
    input logic nor0_out_Y
);
    // No clock/reset in DUT; purely combinational; Y = ~(B1 | (A1 & A2)); sample on $global_clock.

    // Y must equal the a21oi boolean function.
    check_func_equiv: assert property (
        @(posedge $global_clock) Y == ~(B1 | (A1 & A2))
    );

    // Internal AND gate output equals A1 & A2.
    check_and0_out_equiv: assert property (
        @(posedge $global_clock) and0_out == (A1 & A2)
    );

    // Internal NOR gate output equals ~(B1 | and0_out).
    check_nor0_out_equiv: assert property (
        @(posedge $global_clock) nor0_out_Y == ~(B1 | and0_out)
    );

    // Output buffer drives Y equal to nor0_out_Y.
    check_buf0_equiv: assert property (
        @(posedge $global_clock) Y == nor0_out_Y
    );

    // B1 high forces Y low.
    check_b1_high_forces_y_low: assert property (
        @(posedge $global_clock) (B1 == 1'b1) |-> (Y == 1'b0)
    );

    // A1&A2 high forces Y low.
    check_a1a2_high_forces_y_low: assert property (
        @(posedge $global_clock) ((A1 & A2) == 1'b1) |-> (Y == 1'b0)
    );

    // Y high implies B1 low and at least one of A1/A2 low.
    check_y_high_implies_inputs: assert property (
        @(posedge $global_clock) (Y == 1'b1) |-> (B1 == 1'b0) && ((A1 == 1'b0) || (A2 == 1'b0))
    );

    // Y low implies B1 high or A1&A2 high.
    check_y_low_implies_inputs: assert property (
        @(posedge $global_clock) (Y == 1'b0) |-> ((B1 == 1'b1) || ((A1 & A2) == 1'b1))
    );

    // With B1 low and exactly one of A1/A2 high, Y must be high.
    check_onehot_a_inputs_when_b1_low_y_high: assert property (
        @(posedge $global_clock) (B1 == 1'b0 && (A1 ^ A2)) |-> (Y == 1'b1)
    );

    // With B1 low and A1 low, Y must be high (independent of A2).
    check_b1_low_a1_low_y_high: assert property (
        @(posedge $global_clock) (B1 == 1'b0 && A1 == 1'b0) |-> (Y == 1'b1)
    );

    // With B1 low and A2 low, Y must be high (independent of A1).
    check_b1_low_a2_low_y_high: assert property (
        @(posedge $global_clock) (B1 == 1'b0 && A2 == 1'b0) |-> (Y == 1'b1)
    );

endmodule