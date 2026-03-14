module counter4_sva (
    input  logic        clk,
    input  logic        enable,
    input  logic        reset,
    input  logic [3:0]  out
);
    // During reset, out is forced to 0 on each clock.
    check_reset_forces_zero: assert property (
        @(posedge clk) reset |-> (out == 4'd0)
    );

    // If previous cycle was not in reset and enable was 0, out holds its value.
    check_hold_when_prev_disabled: assert property (
        @(posedge clk) disable iff (reset)
            (!$past(reset) && !$past(enable)) |-> (out == $past(out))
    );

    // If previous cycle was not in reset and enable was 1, out increments by 1 modulo 16.
    check_increment_when_prev_enabled: assert property (
        @(posedge clk) disable iff (reset)
            (!$past(reset) && $past(enable)) |-> (out == (($past(out) + 4'd1) & 4'hF))
    );

    // When previous value was 15 and enable was 1 (no reset), counter wraps to 0.
    check_wrap_from_max_with_enable: assert property (
        @(posedge clk) disable iff (reset)
            (!$past(reset) && $past(enable) && ($past(out) == 4'hF)) |-> (out == 4'h0)
    );
endmodule