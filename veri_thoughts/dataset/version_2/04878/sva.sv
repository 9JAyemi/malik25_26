module d_flip_flop_sva (
    input logic D,
    input logic CLK,
    input logic RESET,
    input logic Q
);

    // Q matches the previous clock's reset-or-data update.
    check_state_update: assert property (
        @(posedge CLK)
        !$initstate |-> (Q == ($past(RESET) ? 1'b0 : $past(D)))
    );

    // On consecutive non-reset clocks, Q captures the previous D.
    check_capture_d_after_nonreset: assert property (
        @(posedge CLK) disable iff (RESET)
        !$initstate && !$past(RESET) |-> (Q == $past(D))
    );

    // A reset clock forces Q low by the next sampled cycle.
    check_reset_clears_q: assert property (
        @(posedge CLK)
        RESET |=> (Q == 1'b0)
    );

    // After reset is released, Q is still low on that sampled cycle.
    check_q_low_after_reset_release: assert property (
        @(posedge CLK) disable iff (RESET)
        !$initstate && $past(RESET) |-> (Q == 1'b0)
    );

endmodule