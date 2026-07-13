module d_ff_ar_assertions (
    input logic clk,
    input logic ar,
    input logic D,
    input logic Q
);

    // When asynchronous reset is active, Q must be low at the sampled clock edge.
    check_reset_active_forces_q_low: assert property (
        @(posedge clk) disable iff ($initstate)
        !ar |-> (Q == 1'b0)
    );

    // A prior low reset or prior low D cannot leave Q high on the next sampled clock.
    check_prior_low_condition_keeps_q_low: assert property (
        @(posedge clk) disable iff (!ar || $initstate)
        (!$past(ar) || !$past(D)) |-> (Q == 1'b0)
    );

    // A high Q must come from a prior clock with reset released and D high.
    check_q_high_requires_prior_high_capture: assert property (
        @(posedge clk) disable iff (!ar || $initstate)
        Q |-> ($past(ar) && $past(D))
    );

endmodule