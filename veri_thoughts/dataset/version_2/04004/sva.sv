module counter_assertions (
    input logic       clk,
    input logic       rst,
    input logic       enable,
    input logic [3:0] out
);

    // Synchronous reset clears the counter on the following clock.
    check_reset_clears_out: assert property (
        @(posedge clk) rst |=> (out == 4'h0)
    );

    // When enabled below 15, the counter increments by one.
    check_increment_when_enabled: assert property (
        @(posedge clk) disable iff (rst)
        enable && (out != 4'hF) |=> (out == ($past(out) + 4'h1))
    );

    // When enabled at 15, the counter wraps back to zero.
    check_wrap_from_max: assert property (
        @(posedge clk) disable iff (rst)
        enable && (out == 4'hF) |=> (out == 4'h0)
    );

    // When not enabled, the counter holds its value.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (rst)
        !enable |=> (out == $past(out))
    );

endmodule