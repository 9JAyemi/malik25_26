module counter_4bit_sva (
    input logic clk,
    input logic rst,
    input logic en,
    input logic [3:0] out
);

    // Reset drives the counter to zero on the following clock.
    check_reset_clears_out: assert property (
        @(posedge clk) rst |=> (out == 4'b0000)
    );

    // Reset overrides enable when both are asserted.
    check_reset_priority_over_enable: assert property (
        @(posedge clk) (rst && en) |=> (out == 4'b0000)
    );

    // When enabled below max value, the counter increments by one.
    check_increment_when_enabled: assert property (
        @(posedge clk) disable iff (rst) (en && (out != 4'hF)) |=> (out == ($past(out) + 4'd1))
    );

    // When enabled at max value, the counter wraps to zero.
    check_wrap_from_max: assert property (
        @(posedge clk) disable iff (rst) (en && (out == 4'hF)) |=> (out == 4'h0)
    );

    // When not enabled, the counter holds its value.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (rst) (!en) |=> (out == $past(out))
    );

endmodule