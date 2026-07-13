module counter_sva (
    input logic clk,
    input logic rst,                // active-high reset
    input logic [31:0] max_value,
    input logic [31:0] count
);
    // Reset high at a clock edge forces count to 0 on the next cycle.
    check_reset_next_zero: assert property (
        @(posedge clk) rst |=> (count == 32'd0)
    );

    // While reset stays high across cycles, count must be 0.
    check_reset_holds_zero: assert property (
        @(posedge clk) (rst && $past(rst)) |-> (count == 32'd0)
    );

    // If not in reset and count != max_value-1, next count increments by 1.
    check_increment_when_not_wrap: assert property (
        @(posedge clk) disable iff (rst) (count != (max_value - 32'd1)) |-> ##1 (count == $past(count) + 32'd1)
    );

    // If not in reset and count == max_value-1, next count wraps to 0.
    check_wrap_when_threshold: assert property (
        @(posedge clk) disable iff (rst) (count == (max_value - 32'd1)) |-> ##1 (count == 32'd0)
    );

    // On the first cycle after reset deasserts, next update from 0 follows normal rule.
    check_post_reset_first_update: assert property (
        @(posedge clk) ($past(rst) && !rst) |-> ##1 (count == (($past(max_value) == 32'd1) ? 32'd0 : 32'd1))
    );
endmodule