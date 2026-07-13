module counter_sva (
    input logic CLK,
    input logic RST,
    input logic [3:0] Q
);

    ///// Reset behavior /////
    // When RST is high, Q must be 0 on the next cycle.
    check_reset_clears_Q_next: assert property (
        @(posedge CLK) RST |=> (Q == 4'h0)
    );

    // If RST is high in two consecutive cycles, Q must be 0 in the second cycle.
    check_Q_zero_while_reset_held: assert property (
        @(posedge CLK) (RST && $past(RST)) |-> (Q == 4'h0)
    );

    // Immediately after a reset cycle (RST was 1 last cycle, now 0), Q must be 0.
    check_Q_zero_immediately_after_reset_release: assert property (
        @(posedge CLK) (!RST && $past(RST)) |-> (Q == 4'h0)
    );

    // On a rising edge of RST, Q must be 0 on the next cycle.
    check_next_after_reset_assert_zero: assert property (
        @(posedge CLK) $rose(RST) |=> (Q == 4'h0)
    );

    // On a falling edge of RST, Q must increment on the next cycle.
    check_next_after_reset_release_increments: assert property (
        @(posedge CLK) $fell(RST) |=> (Q == $past(Q) + 1)
    );

    ///// Counting behavior (when not in reset) /////
    // When not in reset, Q increments by 1 each cycle.
    check_increment_when_not_reset: assert property (
        @(posedge CLK) disable iff (RST) 1'b1 |=> (Q == $past(Q) + 1)
    );

    // When not in reset, Q must change every cycle (no hold).
    check_counter_advances_each_cycle: assert property (
        @(posedge CLK) disable iff (RST) 1'b1 |=> (Q != $past(Q))
    );

    // When not in reset and Q is 0xF, it wraps to 0 on the next cycle.
    check_wrap_from_max_when_not_reset: assert property (
        @(posedge CLK) disable iff (RST) (Q == 4'hF) |=> (Q == 4'h0)
    );

    // When not in reset and Q is 0xE, it becomes 0xF on the next cycle.
    check_increment_from_E_to_F_when_not_reset: assert property (
        @(posedge CLK) disable iff (RST) (Q == 4'hE) |=> (Q == 4'hF)
    );

    ///// Unified next-state rule /////
    // Next Q equals 0 if RST was 1 last cycle, else equals last Q + 1.
    check_unified_next_state_rule: assert property (
        @(posedge CLK) 1'b1 |=> ( $past(RST) ? (Q == 4'h0) : (Q == $past(Q) + 1) )
    );

endmodule