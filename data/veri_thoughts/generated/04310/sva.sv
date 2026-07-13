module d_latch_with_reset_and_enable_sva (
    input logic clk,
    input logic D,
    input logic EN,
    input logic RESET,
    input logic Q,
    input logic Q_n
);

    // Reset drives Q low on the next sampled cycle.
    check_reset_forces_q_low: assert property (
        @(posedge clk) RESET |=> (Q == 1'b0)
    );

    // Reset drives Q_n high on the next sampled cycle.
    check_reset_forces_qn_high: assert property (
        @(posedge clk) RESET |=> (Q_n == 1'b1)
    );

    // When enabled, Q captures D.
    check_enable_loads_q_from_d: assert property (
        @(posedge clk) disable iff (RESET) EN |=> (Q == $past(D))
    );

    // When enabled, Q_n captures the inverse of D.
    check_enable_loads_qn_from_inverted_d: assert property (
        @(posedge clk) disable iff (RESET) EN |=> (Q_n == ~$past(D))
    );

    // When not enabled, Q holds its previous value.
    check_hold_q_when_disabled: assert property (
        @(posedge clk) disable iff (RESET) !EN |=> $stable(Q)
    );

    // When not enabled, Q_n holds its previous value.
    check_hold_qn_when_disabled: assert property (
        @(posedge clk) disable iff (RESET) !EN |=> $stable(Q_n)
    );

endmodule