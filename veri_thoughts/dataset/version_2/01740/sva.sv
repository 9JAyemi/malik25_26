module counter_sva (
    input logic clk,
    input logic rst,
    input logic [3:0] count
);

    // While reset is asserted at a clock edge, count must be 0 on the next clock.
    reset_clears_next: assert property (
        @(posedge clk) rst |=> (count == 4'd0)
    );

    // If reset is held high across consecutive clocks, count is 0 at the current clock.
    reset_hold_zero_now: assert property (
        @(posedge clk) ($past(rst) && rst) |-> (count == 4'd0)
    );

    // If reset is held high across consecutive clocks, count was 0 at the previous clock.
    reset_hold_zero_prev: assert property (
        @(posedge clk) ($past(rst) && rst) |-> ($past(count) == 4'd0)
    );

    // Out of reset, count value is always within 0..9.
    count_in_range: assert property (
        @(posedge clk) disable iff (rst) (count <= 4'd9)
    );

    // Whenever count is 9 at a clock edge (out of reset), the next value is 0.
    wrap_from_9_to_0: assert property (
        @(posedge clk) disable iff (rst) (count == 4'd9) |=> (count == 4'd0)
    );

    // If previous clock was in reset, the current count is 0.
    prev_reset_implies_zero_now: assert property (
        @(posedge clk) $past(rst) |-> (count == 4'd0)
    );

endmodule