module binary_counter_sva (
    input logic clk,
    input logic rst,
    input logic load,
    input logic [3:0] data,
    input logic [3:0] count
);
    // If reset was LOW in the previous cycle, count must be 0 now.
    prev_reset_low_clears_now: assert property (
        @(posedge clk) $past(!rst) |-> (count == 4'b0)
    );

    // If reset is LOW this cycle, count must be 0 at the next cycle.
    reset_low_clears_next: assert property (
        @(posedge clk) !rst |-> ##1 (count == 4'b0)
    );

    // After a non-load cycle with reset HIGH, either increment by 1 (mod 16) or got reset to 0.
    increment_or_zero: assert property (
        @(posedge clk) disable iff (!rst)
            ($past(rst) && !$past(load)) |-> ((count == (($past(count) + 4'd1)[3:0])) || (count == 4'b0))
    );

    // After a load cycle with reset HIGH, either equals loaded data or got reset to 0.
    load_or_zero: assert property (
        @(posedge clk) disable iff (!rst)
            ($past(rst) && $past(load)) |-> ((count == $past(data)) || (count == 4'b0))
    );

    // From max value with no load and reset HIGH, wrap to 0 next cycle.
    wrap_from_max_no_load: assert property (
        @(posedge clk) disable iff (!rst)
            ($past(rst) && !$past(load) && ($past(count) == 4'hF)) |-> (count == 4'h0)
    );

    // If a zero was loaded (with reset HIGH), the next observed count must be 0.
    load_zero_results_zero: assert property (
        @(posedge clk) disable iff (!rst)
            ($past(rst) && $past(load) && ($past(data) == 4'h0)) |-> (count == 4'h0)
    );
endmodule