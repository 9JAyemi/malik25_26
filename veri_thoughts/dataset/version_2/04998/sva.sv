module binary_counter_sva (
    input logic clk,
    input logic rst,
    input logic en,
    input logic [3:0] q
);

    // Active-low reset forces the counter output to zero.
    check_reset_clears_q: assert property (
        @(posedge clk) !rst |-> (q == 4'b0000)
    );

    // When enabled, the counter increments by one on the next cycle.
    check_increment_when_enabled: assert property (
        @(posedge clk) disable iff (!rst) en |=> (q == ($past(q) + 4'b0001))
    );

    // When disabled, the counter holds its value on the next cycle.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (!rst) !en |=> (q == $past(q))
    );

    // Counting wraps from 4'hF back to 4'h0 when enabled.
    check_wrap_from_max: assert property (
        @(posedge clk) disable iff (!rst) (en && (q == 4'hF)) |=> (q == 4'h0)
    );

    // After reset release with enable high, the first counted value is 1.
    check_first_count_after_reset_release: assert property (
        @(posedge clk) disable iff (!rst) ($rose(rst) && en) |=> (q == 4'b0001)
    );

    // After reset release with enable low, the counter remains at zero.
    check_hold_zero_after_reset_release: assert property (
        @(posedge clk) disable iff (!rst) ($rose(rst) && !en) |=> (q == 4'b0000)
    );

endmodule