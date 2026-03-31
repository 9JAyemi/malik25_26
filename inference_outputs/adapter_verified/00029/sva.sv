module binary_counter_sva (
    input logic clk,
    input logic reset,
    input logic enable,
    input logic [3:0] q
);

// Reset drives q to zero on the next clock.
    check_reset_clears_q: assert property (
        @(posedge clk) reset |=> (q == 4'b0000)
    );

// When enabled, q increments by one on the next clock.
    check_increment_when_enabled: assert property (
        @(posedge clk) disable iff (reset) enable |=> (q == ($past(q) + 4'd1))
    );

// When not enabled, q holds its value on the next clock.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (reset) !enable |=> (q == $past(q))
    );

// The 4-bit counter wraps from 15 back to 0 when enabled.
    check_wrap_from_max: assert property (
        @(posedge clk) disable iff (reset) (enable && (q == 4'hF)) |=> (q == 4'h0)
    );

endmodule
