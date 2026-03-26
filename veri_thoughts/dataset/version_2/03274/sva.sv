module dffr_assertions (
    input logic Q,
    input logic D,
    input logic C,
    input logic R
);

    // Reset low at a sampled clock forces Q low by the next clock.
    check_reset_clears_q_next_clock: assert property (
        @(posedge C) !R |=> (Q == 1'b0)
    );

    // With reset high, a sampled 0 on D is captured as 0 on the next clock.
    check_capture_zero_on_clock: assert property (
        @(posedge C) (R && !D) |=> (Q == 1'b0)
    );

    // A high Q must come from a prior clock with reset high and D high.
    check_q_high_requires_prior_high_input: assert property (
        @(posedge C) disable iff (!R) 1'b1 |=> (Q |-> $past(R && D))
    );

endmodule