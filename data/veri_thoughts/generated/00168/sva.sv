module d_ff_sync_reset_sva (
    input logic CLK,
    input logic D,
    input logic RESET,
    input logic Q,
    input logic Q_N
);

    // A sampled reset drives the outputs to the reset state by the next clock.
    check_reset_state: assert property (
        @(posedge CLK) RESET |=> (Q == 1'b0 && Q_N == 1'b1)
    );

    // Without reset, Q captures D on the next clock.
    check_q_captures_d: assert property (
        @(posedge CLK) disable iff (RESET) 1'b1 |=> (Q == $past(D))
    );

    // Without reset, Q_N captures the inverse of D on the next clock.
    check_qn_captures_inverse_d: assert property (
        @(posedge CLK) disable iff (RESET) 1'b1 |=> (Q_N == ~$past(D))
    );

    // Outside reset, the two outputs remain logical complements.
    check_outputs_are_complements: assert property (
        @(posedge CLK) disable iff (RESET) (Q_N == ~Q)
    );

endmodule