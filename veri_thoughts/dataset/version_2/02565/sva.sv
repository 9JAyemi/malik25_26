module up_down_counter_sva (
    input logic CLK,
    input logic UP_DOWN,
    input logic RESET,
    input logic [3:0] Q
);

    ///// Reset behavior /////
    // RESET drives Q to zero on the next clock.
    reset_clears_next: assert property (
        @(posedge CLK) RESET |=> (Q == 4'b0000)
    );

    // While RESET is held across cycles, Q remains zero.
    reset_holds_zero: assert property (
        @(posedge CLK) $past(RESET) && RESET |-> (Q == 4'b0000)
    );

    // On RESET deassertion edge, Q is zero in that cycle.
    q_zero_on_reset_fall: assert property (
        @(posedge CLK) $fell(RESET) |-> (Q == 4'b0000)
    );

    ///// Counting behavior /////
    // When UP_DOWN=1 and not in reset, Q increments by 1 on the next clock.
    count_up_step: assert property (
        @(posedge CLK) disable iff (RESET) UP_DOWN |=> (Q == $past(Q) + 4'd1)
    );

    // When UP_DOWN=0 and not in reset, Q decrements by 1 on the next clock.
    count_down_step: assert property (
        @(posedge CLK) disable iff (RESET) !UP_DOWN |=> (Q == $past(Q) - 4'd1)
    );

    // Without reset, Q changes every cycle (always +/-1).
    q_changes_each_cycle: assert property (
        @(posedge CLK) disable iff (RESET) 1'b1 |=> (Q != $past(Q))
    );

    // When counting up from 0xF, Q wraps to 0 on the next clock.
    count_up_wrap_to_zero: assert property (
        @(posedge CLK) disable iff (RESET) (UP_DOWN && (Q == 4'hF)) |=> (Q == 4'h0)
    );

    // When counting down from 0, Q wraps to 0xF on the next clock.
    count_down_wrap_to_f: assert property (
        @(posedge CLK) disable iff (RESET) (!UP_DOWN && (Q == 4'h0)) |=> (Q == 4'hF)
    );

    // Two consecutive UP cycles (no reset) advance Q by +2 modulo 16.
    two_cycles_up: assert property (
        @(posedge CLK) disable iff (RESET) (UP_DOWN ##1 UP_DOWN) |=> (Q == $past(Q,2) + 4'd2)
    );

    // Two consecutive DOWN cycles (no reset) decrement Q by -2 modulo 16.
    two_cycles_down: assert property (
        @(posedge CLK) disable iff (RESET) ((!UP_DOWN) ##1 (!UP_DOWN)) |=> (Q == $past(Q,2) - 4'd2)
    );

endmodule