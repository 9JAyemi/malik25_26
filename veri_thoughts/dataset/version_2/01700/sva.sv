module d_ff_with_async_reset_set_sva (
    input logic Q,
    input logic CLK,
    input logic D,
    input logic SET_B,
    input logic RESET_B
);

    // When RESET_B is HIGH at the clock edge, Q is driven LOW in that cycle.
    reset_forces_zero_now: assert property (
        @(posedge CLK) RESET_B |-> (Q == 1'b0)
    );

    // When SET_B is HIGH and RESET_B is LOW at the clock edge, Q is driven HIGH in that cycle.
    set_forces_one_when_no_reset: assert property (
        @(posedge CLK) disable iff (RESET_B) SET_B |-> (Q == 1'b1)
    );

    // When both RESET_B and SET_B are LOW at the clock edge, Q equals D in that cycle.
    capture_d_when_no_controls: assert property (
        @(posedge CLK) disable iff (RESET_B || SET_B) 1'b1 |-> (Q == D)
    );

    // If both RESET_B and SET_B are HIGH, RESET_B has priority and Q is LOW in that cycle.
    reset_priority_over_set: assert property (
        @(posedge CLK) (RESET_B && SET_B) |-> (Q == 1'b0)
    );

    // If Q is HIGH at the clock edge, then RESET_B must be LOW and either SET_B is HIGH or (SET_B is LOW and D is HIGH).
    q_one_implies_cause: assert property (
        @(posedge CLK) (Q == 1'b1) |-> (!RESET_B && (SET_B || (!SET_B && (D == 1'b1))))
    );

    // If Q is LOW at the clock edge, then either RESET_B is HIGH or (RESET_B and SET_B are LOW and D is LOW).
    q_zero_implies_cause: assert property (
        @(posedge CLK) (Q == 1'b0) |-> (RESET_B || (!RESET_B && !SET_B && (D == 1'b0)))
    );

endmodule