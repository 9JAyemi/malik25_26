module d_ff_res_sva (
    input logic Q,
    input logic D,
    input logic CLK,
    input logic RESET
);

    // Reset forces Q low.
    check_reset_forces_q_low: assert property (
        @(posedge CLK) !RESET |-> (Q == 1'b0)
    );

    // Q is still low on the first clock after reset is released.
    check_q_low_on_reset_release: assert property (
        @(posedge CLK) disable iff (!RESET) $rose(RESET) |-> (Q == 1'b0)
    );

    // With reset high, Q reflects D from the previous clock.
    check_q_captures_previous_d: assert property (
        @(posedge CLK) disable iff (!RESET) 1'b1 |=> (Q == $past(D))
    );

endmodule