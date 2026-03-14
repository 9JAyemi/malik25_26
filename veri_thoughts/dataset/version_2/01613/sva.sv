module counter_sva (
    input logic Clk,
    input logic Reset,     // Active-HIGH synchronous reset
    input logic Enable,
    input logic [3:0] Q
);

    ///// Reset behavior /////
    // On any cycle with Reset HIGH, Q is 0 on the next cycle.
    reset_forces_zero_next: assert property (
        @(posedge Clk) Reset |=> (Q == 4'd0)
    );

    // If Reset is held HIGH for consecutive cycles, Q must read 0.
    reset_hold_zero: assert property (
        @(posedge Clk) (Reset && $past(Reset)) |-> (Q == 4'd0)
    );

    ///// Enable/hold/increment rules /////
    // When disabled (and not in reset), Q holds its value into the next cycle.
    hold_when_disabled: assert property (
        @(posedge Clk) disable iff (Reset) (!Enable) |=> (Q == $past(Q))
    );

    // When enabled and Q != 15, Q increments by 1 next cycle.
    increment_when_enabled_no_overflow: assert property (
        @(posedge Clk) disable iff (Reset) (Enable && (Q != 4'hF)) |=> (Q == $past(Q) + 4'd1)
    );

    // When enabled and Q == 15, Q wraps to 0 next cycle.
    rollover_when_enabled_at_max: assert property (
        @(posedge Clk) disable iff (Reset) (Enable && (Q == 4'hF)) |=> (Q == 4'd0)
    );

    // Any change to Q (without a reset in the previous cycle) requires previous Enable.
    change_requires_prev_enable: assert property (
        @(posedge Clk) disable iff (Reset) ($changed(Q) && !$past(Reset)) |-> $past(Enable)
    );

    // With 16 consecutive enabled cycles (no reset), Q returns to its value 16 cycles earlier.
    wrap_after_16_enables: assert property (
        @(posedge Clk) disable iff (Reset) (Enable[*16]) |=> (Q == $past(Q, 16))
    );

    // With two consecutive disabled cycles (no reset), Q matches its value two cycles earlier.
    hold_across_two_disabled_cycles: assert property (
        @(posedge Clk) disable iff (Reset) (!Enable[*2]) |=> (Q == $past(Q, 2))
    );

endmodule