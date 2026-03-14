module up_counter_sva (
    input logic clk,
    input logic rst,
    input logic [3:0] count
);

    // While reset is asserted LOW at a clock edge, count must be 0.
    check_reset_forces_zero: assert property (
        @(posedge clk) !rst |-> (count == 4'd0)
    );

    // If reset is LOW on two consecutive clock edges, count remains 0.
    check_zero_while_reset_low_consecutive: assert property (
        @(posedge clk) (!rst && $past(!rst)) |-> (count == 4'd0)
    );

    // On a sampled falling edge of reset, count is 0 at that clock edge.
    check_zero_on_reset_fall: assert property (
        @(posedge clk) $fell(rst) |-> (count == 4'd0)
    );

    // On the first clock edge after reset deasserts (LOW->HIGH), count is 1.
    check_first_count_after_reset_release: assert property (
        @(posedge clk) $rose(rst) |-> (count == 4'd1)
    );

    // When not in reset, count must be a known value (no X/Z).
    check_count_known_when_active: assert property (
        @(posedge clk) disable iff (!rst) !$isunknown(count)
    );

endmodule