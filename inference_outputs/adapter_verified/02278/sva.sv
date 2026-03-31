module slow_oscillator_sva (
    input logic clk,
    input logic rstn,
    input logic [3:0] led,
    input logic osc_clk
);

// Reset forces led to zero on the next clock.
    reset_clears_led: assert property (
        @(posedge clk) !rstn |=> (led == 4'h0)
    );

// Reset forces osc_clk low on the next clock.
    reset_clears_clk: assert property (
        @(posedge clk) !rstn |=> (osc_clk == 1'b0)
    );

// With reset high, led increments by one each cycle.
    led_increments: assert property (
        @(posedge clk) disable iff (!rstn) 1'b1 |=> (led == ($past(led) + 4'd1))
    );

// With reset high, led wraps from 15 back to 0.
    led_wraps_from_max: assert property (
        @(posedge clk) disable iff (!rstn) (led == 4'hF) |=> (led == 4'h0)
    );

// With reset high, osc_clk is low exactly when led is 0.
    clk_low_when_led_zero: assert property (
        @(posedge clk) disable iff (!rstn) (led == 4'h0) |-> (osc_clk == 1'b0)
    );

// With reset high, osc_clk is high exactly when led is not 0.
    clk_high_when_led_nonzero: assert property (
        @(posedge clk) disable iff (!rstn) (led != 4'h0) |-> (osc_clk == 1'b1)
    );

endmodule
