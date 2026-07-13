module binary_counter_sva (
    input logic clk,
    input logic rst,
    input logic en,
    input logic [3:0] out
);

    // A sampled reset leaves the counter at zero by the next clock.
    check_reset_clears_output: assert property (
        @(posedge clk) rst |=> (out == 4'd0)
    );

    // When enabled outside reset, the counter increments by one.
    check_increment_when_enabled: assert property (
        @(posedge clk) disable iff (rst) en |=> (out == ($past(out) + 4'd1))
    );

    // When disabled outside reset, the counter holds its value.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (rst) !en |=> (out == $past(out))
    );

    // When enabled at 15, the 4-bit counter wraps to zero.
    check_wrap_from_max: assert property (
        @(posedge clk) disable iff (rst) (en && (out == 4'hF)) |=> (out == 4'h0)
    );

endmodule