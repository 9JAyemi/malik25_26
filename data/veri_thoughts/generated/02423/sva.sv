module BinaryCounter_sva (
    input logic clk,
    input logic reset,
    input logic [3:0] count
);
    // Next state follows: if previous reset then 0 else previous count + 1 (mod 16).
    check_state_update_from_prev: assert property (
        @(posedge clk) $past(1'b1) |-> (count == ( $past(reset) ? 4'd0 : ($past(count) + 4'd1) ))
    );

    // A reset high sets count to 0 on the next clock.
    check_reset_sets_zero_next: assert property (
        @(posedge clk) reset |=> (count == 4'd0)
    );

    // When not in reset, count increments by 1 each cycle.
    check_increment_by_one_no_reset: assert property (
        @(posedge clk) disable iff (reset) $past(1'b1) |-> (count == ($past(count) + 4'd1))
    );

    // When not in reset and previous count was 15, wrap to 0.
    check_wrap_from_15_to_0: assert property (
        @(posedge clk) disable iff (reset) ($past(1'b1) && ($past(count) == 4'hF)) |-> (count == 4'h0)
    );

    // LSB toggles every increment when not in reset.
    check_lsb_toggles_when_incrementing: assert property (
        @(posedge clk) disable iff (reset) $past(1'b1) |-> (count[0] == ~$past(count[0]))
    );

    // After 16 cycles without reset, count returns to its value from 16 cycles ago.
    check_return_to_prior_after_16_no_reset: assert property (
        @(posedge clk) disable iff (reset) (!reset[*16]) |=> (count == $past(count, 16))
    );

    // If reset is held high across cycles, count stays 0.
    check_hold_zero_while_reset_held: assert property (
        @(posedge clk) ($past(1'b1) && reset && $past(reset)) |-> (count == 4'd0)
    );
endmodule