module d_ff_async_reset_sva (
    input logic D,
    input logic R,
    input logic Q,
    input logic Q_N
);

    // No RTL clock is present; sample on the formal global clock.

    // Reset forces Q low.
    check_q_low_during_reset: assert property (
        @($global_clock) R |-> (Q == 1'b0)
    );

    // Reset forces Q_N high.
    check_qn_high_during_reset: assert property (
        @($global_clock) R |-> (Q_N == 1'b1)
    );

    // When reset is low, Q reflects D.
    check_q_tracks_d_when_not_reset: assert property (
        @($global_clock) disable iff (R) (Q == D)
    );

    // When reset is low, Q_N reflects the inverse of D.
    check_qn_tracks_inv_d_when_not_reset: assert property (
        @($global_clock) disable iff (R) (Q_N == ~D)
    );

    // The outputs are always complementary.
    check_outputs_complementary: assert property (
        @($global_clock) (Q_N == ~Q)
    );

endmodule