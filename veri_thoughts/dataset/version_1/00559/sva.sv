module dff_posedge_reset_sva (
    input logic CLK,
    input logic D,
    input logic reset,
    input logic Q
);

    // A sampled high reset clears Q by the next clock.
    check_reset_clears_q: assert property (
        @(posedge CLK) disable iff ($initstate) reset |=> (Q == 1'b0)
    );

    // A sampled low D drives Q low by the next clock.
    check_zero_data_captures_zero: assert property (
        @(posedge CLK) disable iff ($initstate) (D == 1'b0) |=> (Q == 1'b0)
    );

    // Reset overrides D when both are sampled high.
    check_reset_priority_over_d: assert property (
        @(posedge CLK) disable iff ($initstate) (reset && D) |=> (Q == 1'b0)
    );

    // A high Q must come from a previously sampled high D.
    check_high_q_requires_prior_high_d: assert property (
        @(posedge CLK) disable iff (reset || $initstate) (Q == 1'b1) |-> $past(D == 1'b1)
    );

    // A high Q cannot follow a sampled reset.
    check_high_q_not_after_sampled_reset: assert property (
        @(posedge CLK) disable iff (reset || $initstate) (Q == 1'b1) |-> !$past(reset)
    );

endmodule