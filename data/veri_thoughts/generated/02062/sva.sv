module d_flip_flop_sva (
    input logic D,
    input logic CLK,
    input logic RESET,
    input logic Q
);

    // While RESET is HIGH, Q must be 0 at each CLK edge.
    check_reset_forces_q_zero: assert property (
        @(posedge CLK) RESET |-> (Q == 1'b0)
    );

    // If RESET rose since last CLK edge, Q must be 0 at this CLK edge.
    check_async_reset_rise_clears_q_by_next_clk: assert property (
        @(posedge CLK) $rose(RESET) |-> (Q == 1'b0)
    );

    // If RESET fell since last CLK edge, Q is still 0 at this CLK edge (before capture).
    check_reset_release_q_zero_before_capture: assert property (
        @(posedge CLK) $fell(RESET) |-> (Q == 1'b0)
    );

    // When not in reset on consecutive cycles, Q equals D from the previous cycle.
    check_d_captured_to_q_next_cycle: assert property (
        @(posedge CLK) disable iff (RESET) !$past(RESET) |-> (Q == $past(D))
    );

    // If Q==D at a CLK edge and not crossing reset, Q holds its value at the next CLK.
    check_q_holds_when_q_equals_d: assert property (
        @(posedge CLK) disable iff (RESET) (!$past(RESET) && (Q == D)) |=> (Q == $past(Q))
    );

endmodule