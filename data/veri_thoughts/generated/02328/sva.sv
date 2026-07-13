module counter_sva (
    input logic CLK,
    input logic RST,
    input logic EN,
    input logic [3:0] COUNT
);
    // Clock: CLK (posedge). Reset: RST active-high asynchronous.
    // Sequential 4-bit up-counter with enable; reset clears to 0; EN increments, else holds.

    // On any clock where reset is asserted, COUNT must be 0.
    check_reset_clears_count: assert property (
        @(posedge CLK) RST |-> (COUNT == 4'b0000)
    );

    // Immediately after reset deasserts, if EN is 0 then COUNT remains 0.
    check_hold_after_reset_release_without_en: assert property (
        @(posedge CLK) disable iff (RST) $fell(RST) && !EN |-> (COUNT == 4'b0000)
    );

    // Immediately after reset deasserts, if EN is 1 then COUNT becomes 1.
    check_inc_after_reset_release_with_en: assert property (
        @(posedge CLK) disable iff (RST) $fell(RST) && EN |-> (COUNT == 4'b0001)
    );

    // With no reset in the previous cycle, EN=1 increments COUNT by 1 (mod 16).
    check_increment_on_enable: assert property (
        @(posedge CLK) disable iff (RST) (EN && !$past(RST)) |-> (COUNT == $past(COUNT) + 4'd1)
    );

    // With no reset in the previous cycle, EN=0 holds COUNT constant.
    check_hold_when_disabled: assert property (
        @(posedge CLK) disable iff (RST) (!EN && !$past(RST)) |-> (COUNT == $past(COUNT))
    );

    // With no reset in the previous cycle, wrap from 15 to 0 when EN=1.
    check_wrap_on_max: assert property (
        @(posedge CLK) disable iff (RST) (EN && !$past(RST) && ($past(COUNT) == 4'hF)) |-> (COUNT == 4'h0)
    );

    // With no reset in the last 2 cycles, EN=1 for 2 consecutive cycles increments by 2.
    check_two_cycle_increment_on_enable: assert property (
        @(posedge CLK) disable iff (RST) (EN && $past(EN) && !$past(RST) && !$past(RST,2)) |-> (COUNT == $past(COUNT,2) + 4'd2)
    );

    // With no reset in the last 2 cycles, EN=0 for 2 consecutive cycles holds value over 2 cycles.
    check_two_cycle_hold_when_disabled: assert property (
        @(posedge CLK) disable iff (RST) (!EN && !$past(EN) && !$past(RST) && !$past(RST,2)) |-> (COUNT == $past(COUNT,2))
    );

endmodule