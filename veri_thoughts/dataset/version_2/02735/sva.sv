module RCB_FRL_count_to_16x_sva (
    input logic clk,
    input logic rst,          // active-high asynchronous reset
    input logic count,        // count enable
    input logic [3:0] counter_value
);
    // Reset high at a clock edge forces counter_value to 0.
    check_reset_level_forces_zero: assert property (
        @(posedge clk) rst |-> (counter_value == 4'h0)
    );

    // If reset is held high across consecutive clock edges, value stays 0.
    check_reset_held_keeps_zero: assert property (
        @(posedge clk) (rst && $past(rst)) |-> (counter_value == 4'h0)
    );

    // With no reset across the boundary and count=0, hold last value.
    check_hold_when_count_low: assert property (
        @(posedge clk) disable iff (rst)
            ($past(!rst) && ($past(count) == 1'b0)) |-> (counter_value == $past(counter_value))
    );

    // With no reset across the boundary and count=1, increment by 1 modulo 16.
    check_increment_when_count_high: assert property (
        @(posedge clk) disable iff (rst)
            ($past(!rst) && ($past(count) == 1'b1)) |-> (counter_value == (($past(counter_value) + 4'd1)[3:0]))
    );

    // Explicit wrap-around: from 4'hF with count=1 (no reset across), next is 4'h0.
    check_wrap_on_f_when_enabled: assert property (
        @(posedge clk) disable iff (rst)
            ($past(!rst) && ($past(count) == 1'b1) && ($past(counter_value) == 4'hF)) |-> (counter_value == 4'h0)
    );

    // Combined next-state function (no reset across): next = prev + (count?1:0) modulo 16.
    check_next_state_function: assert property (
        @(posedge clk) disable iff (rst)
            $past(!rst) |-> (counter_value == (($past(counter_value) + ($past(count) ? 4'd1 : 4'd0))[3:0]))
    );
endmodule