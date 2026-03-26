module and_ctrl_sva (
    input logic clk,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic C1,
    input logic CTRL,
    input logic Y
);

    // Y must match the exact combinational equation implemented in the RTL.
    check_y_matches_rtl_equation: assert property (
        @(posedge clk)
        Y == (((CTRL == 1'b0) && A1 && A2 && A3) ||
              ((CTRL == 1'b1) && A1 && A2 && A3 && B1 && !C1) ||
              ((CTRL == 1'b1) && A1 && A2 && A3 && B1 && C1) ||
              ((CTRL == 1'b1) && A1 && A2 && A3 && !B1 && C1))
    );

    // Y can only be high when all three A inputs are high.
    check_y_requires_all_a_inputs: assert property (
        @(posedge clk)
        (!A1 || !A2 || !A3) |-> !Y
    );

    // With CTRL low, Y is the AND of A1, A2, and A3.
    check_ctrl_low_function: assert property (
        @(posedge clk)
        (CTRL == 1'b0) |-> (Y == (A1 && A2 && A3))
    );

    // With CTRL high and B1 high, C1 does not affect Y.
    check_ctrl_high_b1_high_function: assert property (
        @(posedge clk)
        ((CTRL == 1'b1) && B1) |-> (Y == (A1 && A2 && A3))
    );

    // With CTRL high and B1 low, Y depends on C1 along with A1, A2, and A3.
    check_ctrl_high_b1_low_function: assert property (
        @(posedge clk)
        ((CTRL == 1'b1) && !B1) |-> (Y == (A1 && A2 && A3 && C1))
    );

    // With CTRL high and both B1 and C1 low, Y must be low.
    check_ctrl_high_b1_c1_low_blocks_y: assert property (
        @(posedge clk)
        ((CTRL == 1'b1) && !B1 && !C1) |-> !Y
    );

endmodule