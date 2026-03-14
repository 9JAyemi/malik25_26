module up_counter_sva (
    input logic clk,
    input logic reset,        // Active-low asynchronous reset (0 = reset asserted)
    input logic [3:0] out
);

    // When reset is asserted low at a clock edge, out must be zero.
    check_reset_forces_zero: assert property (
        @(posedge clk) !reset |-> (out == 4'h0)
    );

    // On the sampled falling edge of reset, out must be zero.
    check_async_reset_on_fall: assert property (
        @(posedge clk) $fell(reset) |-> (out == 4'h0)
    );

    // While reset stays low across cycles, out holds at zero.
    check_hold_zero_while_reset_low: assert property (
        @(posedge clk) (!reset && !$past(reset)) |-> ($past(out) == 4'h0 && out == 4'h0)
    );

    // With reset high in consecutive cycles, out increments by 1 modulo 16.
    check_increment_when_reset_high: assert property (
        @(posedge clk) disable iff (!reset) $past(reset) |-> out == (($past(out) + 4'd1) & 4'hF)
    );

    // With reset high in consecutive cycles and previous out == 0xF, wrap to 0x0.
    check_wrap_from_F_to_0: assert property (
        @(posedge clk) disable iff (!reset) ($past(reset) && ($past(out) == 4'hF)) |-> (out == 4'h0)
    );

    // Over two cycles with reset high, out advances by +2 modulo 16.
    check_two_cycle_increment: assert property (
        @(posedge clk) disable iff (!reset) ($past(reset,2) && $past(reset,1)) |-> out == (($past(out,2) + 4'd2) & 4'hF)
    );

    // On the sampled rising edge of reset (release), out is still zero at that cycle.
    check_out_zero_on_reset_release: assert property (
        @(posedge clk) disable iff (!reset) $rose(reset) |-> (out == 4'h0)
    );

endmodule