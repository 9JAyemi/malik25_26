module slow_oscillator_sva (
    input logic clk,
    input logic rstn,
    input logic [3:0] led,
    input logic [22:0] c_delay,
    input logic [3:0] q
);

    // Reset clears the delay counter.
    check_reset_clears_delay: assert property (
        @(posedge clk) !rstn |-> (c_delay == 23'h000000)
    );

    // Reset clears the LED output.
    check_reset_clears_led: assert property (
        @(posedge clk) !rstn |-> (led == 4'h0)
    );

    // Reset clears the internal clock output.
    check_reset_clears_clk: assert property (
        @(posedge clk) !rstn |-> (clk == 1'b0)
    );

    // The delay counter increments by one when reset is inactive.
    check_delay_increments: assert property (
        @(posedge clk) disable iff (!rstn) $past(rstn) |-> (c_delay == $past(c_delay) + 23'd1)
    );

    // The delay counter wraps from 23'hFFFFF to 23'h00000.
    check_delay_wraps: assert property (
        @(posedge clk) disable iff (!rstn) ($past(rstn) && ($past(c_delay) == 23'hFFFFF)) |-> (c_delay == 23'h00000)
    );

    // The internal clock output is the MSB of the delay counter.
    check_clk_matches_delay_msb: assert property (
        @(posedge clk) disable iff (!rstn) (clk == c_delay[22])
    );

    // The LED output is the 4-bit counter output.
    check_led_matches_q: assert property (
        @(posedge clk) disable iff (!rstn) (led == q)
    );

    // The LED counter increments by one when reset is inactive.
    check_led_increments: assert property (
        @(posedge clk) disable iff (!rstn) $past(rstn) |-> (led == $past(led) + 4'd1)
    );

    // The LED counter wraps from 4'hF to 4'h0.
    check_led_wraps: assert property (
        @(posedge clk) disable iff (!rstn) ($past(rstn) && ($past(led) == 4'hF)) |-> (led == 4'h0)
    );

endmodule