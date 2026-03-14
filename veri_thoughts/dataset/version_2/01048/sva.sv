module counter_sva #(
  parameter WIDTH = 16
) (
  input  logic                 clk,
  input  logic                 reset,   // active-high synchronous reset
  input  logic                 enable,
  input  logic [WIDTH-1:0]     count
);

    // After a reset cycle, count must be zero on the following cycle.
    check_reset_clears_count: assert property (
        @(posedge clk) disable iff (reset)
            $past(reset) |-> (count == '0)
    );

    // If enable was 1 last cycle (and not in reset), count increments by 1.
    check_increment_on_enable: assert property (
        @(posedge clk) disable iff (reset)
            ($past(!reset) && $past(enable)) |-> (count == $past(count) + 1'b1)
    );

    // If enable was 0 last cycle (and not in reset), count holds its value.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (reset)
            ($past(!reset) && !$past(enable)) |-> (count == $past(count))
    );

    // When enabled at max value (and not in reset), count wraps to zero next cycle.
    check_wrap_on_overflow: assert property (
        @(posedge clk) disable iff (reset)
            ($past(!reset) && $past(enable) && ($past(count) == {WIDTH{1'b1}})) |-> (count == '0)
    );

    // Count may only change if enable was 1 in the previous cycle (excluding reset effect).
    check_change_requires_enable: assert property (
        @(posedge clk) disable iff (reset)
            ($past(!reset) && (count != $past(count))) |-> $past(enable)
    );

    // Reset overrides enable: if reset was 1 last cycle, count is zero now.
    check_reset_overrides_enable: assert property (
        @(posedge clk) disable iff (reset)
            ($past(reset) && $past(enable)) |-> (count == '0)
    );

    // If enable was 0 for two consecutive cycles with no reset, value equals two-cycles-ago.
    check_hold_two_cycles_when_disabled: assert property (
        @(posedge clk) disable iff (reset)
            (!$past(reset) && !$past(reset,2) && !$past(enable) && !$past(enable,2)) |-> (count == $past(count,2))
    );

endmodule