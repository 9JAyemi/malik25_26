module d_ff_reset_sva (
    input logic D,
    input logic RESET_B,
    input logic CLK,
    input logic Q
);

    // Active-low reset clears Q.
    check_reset_forces_q_low: assert property (
        @(posedge CLK)
        !RESET_B |-> (Q == 1'b0)
    );

    // Q stays low on the first clock after reset was active.
    check_release_edge_keeps_q_low: assert property (
        @(posedge CLK) disable iff ($initstate || !RESET_B)
        !$past(RESET_B) |-> (Q == 1'b0)
    );

    // A prior sampled low D produces a low Q.
    check_low_d_captures_low: assert property (
        @(posedge CLK) disable iff ($initstate || !RESET_B)
        ($past(RESET_B) && ($past(D) == 1'b0)) |-> (Q == 1'b0)
    );

    // A high Q must come from a prior sampled high D.
    check_high_q_requires_prior_high_d: assert property (
        @(posedge CLK) disable iff ($initstate || !RESET_B)
        (Q == 1'b1) |-> ($past(RESET_B) && ($past(D) == 1'b1))
    );

    // A rising Q must be caused by a prior sampled high D.
    check_q_rise_requires_prior_high_d: assert property (
        @(posedge CLK) disable iff ($initstate || !RESET_B)
        $rose(Q) |-> ($past(RESET_B) && ($past(D) == 1'b1))
    );

endmodule