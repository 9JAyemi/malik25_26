module counter_4bit_sva (
    input logic clk,
    input logic reset,
    input logic enable,
    input logic [3:0] count
);
    // Reset low forces count to zero on each clock.
    check_reset_forces_zero: assert property (
        @(posedge clk) !reset |-> (count == 4'b0000)
    );

    // While reset stays low across cycles, count remains zero and stable.
    check_hold_zero_while_reset: assert property (
        @(posedge clk) (!reset && $past(!reset)) |-> (count == 4'b0000 && $stable(count))
    );

    // Next-state function when out of reset: increment on enable, else hold.
    check_next_state_function: assert property (
        @(posedge clk) disable iff (!reset) $past(reset) |-> (count == (enable ? ($past(count) + 4'd1) : $past(count)))
    );

    // When enable is 1, count increments by exactly 1 (mod 16).
    check_increment_when_enable: assert property (
        @(posedge clk) disable iff (!reset) ($past(reset) && enable) |-> (count == ($past(count) + 4'd1))
    );

    // When enable is 0, count holds its previous value.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (!reset) ($past(reset) && !enable) |-> (count == $past(count))
    );

    // Wrap-around: from 4'hF with enable high, next value is 0.
    check_wrap_on_max: assert property (
        @(posedge clk) disable iff (!reset) ($past(reset) && enable && ($past(count) == 4'hF)) |-> (count == 4'h0)
    );

    // If reset rises on a clock edge, next count is 1 if enable=1 else 0.
    check_release_from_reset_at_clk: assert property (
        @(posedge clk) $rose(reset) |-> (count == (enable ? 4'd1 : 4'd0))
    );
endmodule