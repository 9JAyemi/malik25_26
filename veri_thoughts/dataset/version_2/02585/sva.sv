module d_ff_asynchronous_set_sva (
    input logic CLK,
    input logic D,
    input logic SET_B, // Active-low asynchronous clear
    input logic Q
);

    // When SET_B is LOW at a clock edge, Q must be 0 on the next clock.
    clear_forces_q0_next: assert property (
        @(posedge CLK) !SET_B |-> (Q == 1'b0)
    );

    // If SET_B is LOW for two consecutive clocks, Q is 0 at the current clock.
    q0_when_clear_two_cycles: assert property (
        @(posedge CLK) (!SET_B && $past(!SET_B)) |=> (Q == 1'b0)
    );

    // If SET_B was LOW on the previous clock, Q is 0 on the current clock.
    q0_when_prev_clear: assert property (
        @(posedge CLK) $past(!SET_B) |-> (Q == 1'b0)
    );

    // On deassertion of SET_B (LOW->HIGH), Q remains 0 at that clock edge.
    deassertion_holds_q0_this_clk: assert property (
        @(posedge CLK) $rose(SET_B) |=> (Q == 1'b0)
    );

    // If Q rises, the previous clock must have captured D==1 with SET_B HIGH.
    q_rise_implies_prev_capture_of_one: assert property (
        @(posedge CLK) disable iff (!SET_B) $rose(Q) |-> ($past(SET_B) && $past(D))
    );

    // While SET_B stays LOW across clocks, Q remains stable (holds 0).
    q_stable_during_persistent_clear: assert property (
        @(posedge CLK) (!SET_B && $past(!SET_B)) |=> $stable(Q)
    );

endmodule