module slow_oscillator_sva (
    input logic clk,
    input logic rstn,
    input logic [3:0] led,
    input logic [22:0] c_delay,
    input logic [3:0] q
);

    // Reset clears the delay counter.
    check_reset_clears_c_delay: assert property (
        @(posedge clk) !rstn |-> (c_delay == 23'h0000000)
    );

    // Reset clears the LED output.
    check_reset_clears_led: assert property (
        @(posedge clk) !rstn |-> (led == 4'h0)
    );

    // The delay counter increments by one when reset is inactive.
    check_c_delay_increments: assert property (
        @(posedge clk) disable iff (!rstn)
        1'b1 |=> (c_delay == ($past(c_delay) + 23'h0000001))
    );

    // The delay counter wraps from 23'hFFFFF to 23'h00000.
    check_c_delay_wraps: assert property (
        @(posedge clk) disable iff (!rstn)
        (c_delay == 23'hFFFFF) |=> (c_delay == 23'h00000)
    );

    // The LED output increments by one when reset is inactive.
    check_led_increments: assert property (
        @(posedge clk) disable iff (!rstn)
        1'b1 |=> (led == ($past(led) + 4'h1))
    );

    // The LED output wraps from 4'hF to 4'h0.
    check_led_wraps: assert property (
        @(posedge clk) disable iff (!rstn)
        (led == 4'hF) |=> (led == 4'h0)
    );

    // The LED output matches the internal 4-bit counter.
    check_led_matches_q: assert property (
        @(posedge clk) disable iff (!rstn)
        (led == q)
    );

    // The output clock is the MSB of the delay counter.
    check_clk_matches_c_delay_msb: assert property (
        @(posedge clk) disable iff (!rstn)
        (clk == c_delay[22])
    );

endmodule