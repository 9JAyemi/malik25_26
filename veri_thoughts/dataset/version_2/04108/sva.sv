module up_counter_assertions (
    input logic       clock,
    input logic       reset,
    input logic       count_enable,
    input logic [3:0] Q
);

    // Reset clears the counter on the next clock sample.
    check_reset_clears_q: assert property (
        @(posedge clock) reset |=> (Q == 4'b0000)
    );

    // Reset has priority even when count enable is high.
    check_reset_priority_over_enable: assert property (
        @(posedge clock) reset && count_enable |=> (Q == 4'b0000)
    );

    // When enabled without reset, the counter increments by one.
    check_increment_when_enabled: assert property (
        @(posedge clock) disable iff (reset) count_enable |=> (Q == ($past(Q) + 4'd1))
    );

    // When disabled without reset, the counter holds its value.
    check_hold_when_disabled: assert property (
        @(posedge clock) disable iff (reset) !count_enable |=> (Q == $past(Q))
    );

endmodule