module sync_seq_circuit_sva (
    input logic Q,
    input logic CLK_N,
    input logic D,
    input logic RESET_B
);

    // A sampled low reset forces Q low by the next clock.
    check_reset_forces_q_low: assert property (
        @(posedge CLK_N) (!RESET_B) |=> (Q == 1'b0)
    );

    // A sampled rise of Q can only come from D being high on the prior clock.
    check_q_rise_requires_prior_d: assert property (
        @(posedge CLK_N) disable iff (!RESET_B)
        (!$initstate && $rose(Q)) |-> $past(D)
    );

    // A sampled rise of Q requires reset to have been released on the prior clock.
    check_q_rise_requires_prior_reset_release: assert property (
        @(posedge CLK_N) disable iff (!RESET_B)
        (!$initstate && $rose(Q)) |-> $past(RESET_B)
    );

    // A high Q must come from a prior high Q or a prior set request.
    check_q_high_has_valid_prior_source: assert property (
        @(posedge CLK_N) disable iff (!RESET_B)
        (!$initstate && Q) |-> ($past(RESET_B) && ($past(Q) || $past(D)))
    );

    // If Q was low and D was low with reset released, Q stays low at the next sample.
    check_low_q_holds_without_set: assert property (
        @(posedge CLK_N) disable iff (!RESET_B)
        (!$initstate && $past(RESET_B) && !$past(Q) && !$past(D)) |-> !Q
    );

    // Without a prior D high, Q cannot show a sampled low-to-high transition.
    check_no_q_rise_without_prior_set: assert property (
        @(posedge CLK_N) disable iff (!RESET_B)
        (!$initstate && !$past(D)) |-> !$rose(Q)
    );

endmodule