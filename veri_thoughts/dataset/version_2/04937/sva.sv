module register16_with_enable_sva (
    input logic clk,
    input logic [15:0] in,
    input logic write,
    input logic reset,
    input logic enable,
    input logic [15:0] out
);

    // Reset clears the register on the next sampled cycle.
    check_reset_clears_out: assert property (
        @(posedge clk) reset |=> (out == 16'b0)
    );

    // Reset overrides a simultaneous enabled write.
    check_reset_priority_over_write: assert property (
        @(posedge clk) (reset && enable && write) |=> (out == 16'b0)
    );

    // An enabled write loads the input value.
    check_capture_on_write: assert property (
        @(posedge clk) disable iff (reset) (enable && write) |=> (out == $past(in))
    );

    // When disabled, the register holds its value.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (reset) (!enable) |=> (out == $past(out))
    );

    // When enabled without write, the register holds its value.
    check_hold_when_no_write: assert property (
        @(posedge clk) disable iff (reset) (enable && !write) |=> (out == $past(out))
    );

    // Write has no effect unless enable is high.
    check_write_ignored_without_enable: assert property (
        @(posedge clk) disable iff (reset) (!enable && write) |=> (out == $past(out))
    );

endmodule