module binary_counter_sva (
    input logic       clk,
    input logic       reset,
    input logic       enable,
    input logic [3:0] out
);

    // A sampled reset clears the counter on the next clock.
    check_reset_clears_out: assert property (
        @(posedge clk) reset |=> (out == 4'b0000)
    );

    // Reset has priority over enable when both are high.
    check_reset_overrides_enable: assert property (
        @(posedge clk) (reset && enable) |=> (out == 4'b0000)
    );

    // When enabled outside reset, the counter increments by one.
    check_increment_when_enabled: assert property (
        @(posedge clk) disable iff (reset)
        enable |=> (out == ($past(out) + 4'd1))
    );

    // When disabled outside reset, the counter holds its value.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (reset)
        !enable |=> (out == $past(out))
    );

    // Incrementing from 4'hF wraps the counter to 4'h0.
    check_wrap_from_max: assert property (
        @(posedge clk) disable iff (reset)
        (enable && (out == 4'hF)) |=> (out == 4'h0)
    );

endmodule