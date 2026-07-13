module binary_counter_sva (
    input logic E,
    input logic s_aclk,
    input logic AR,
    input logic [3:0] Q
);

// Clock: s_aclk (posedge). Reset: AR (active-high synchronous). Logic: sequential counter.

    // When AR is high, Q is cleared to 0 on the next cycle.
    check_async_reset_clears_q: assert property (
        @(posedge s_aclk) AR |=> (Q == 4'b0000)
    );

// When E is high and Q is not at max, Q increments by 1 on the next cycle.
    check_increment_when_enabled_not_max: assert property (
        @(posedge s_aclk) disable iff (AR) E && (Q != 4'b1111) |=> (Q == ($past(Q) + 4'd1))
    );

// When E is high and Q is at max, Q wraps to 0 on the next cycle.
    check_wrap_when_enabled_at_max: assert property (
        @(posedge s_aclk) disable iff (AR) E && (Q == 4'b1111) |=> (Q == 4'b0000)
    );

// When E is low, Q holds its value on the next cycle.
    check_hold_when_disabled: assert property (
        @(posedge s_aclk) disable iff (AR) !E |=> (Q == $past(Q))
    );

// Q can only change when AR is low and E is high.
    check_q_change_requires_enable: assert property (
        @(posedge s_aclk) disable iff (AR) (Q != $past(Q)) |-> (AR == 1'b0) && (E == 1'b1)
    );

// If E is high and Q is 0, the next value must be 1 (no wrap).
    check_increment_from_zero: assert property (
        @(posedge s_aclk) disable iff (AR) E && (Q == 4'b0000) |=> (Q == 4'b0001)
    );

endmodule
