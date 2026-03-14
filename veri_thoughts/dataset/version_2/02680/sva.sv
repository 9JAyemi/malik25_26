module counter16_sva (
    input logic clk,
    input logic rst,
    input logic [15:0] count
);

    // On synchronous reset, next cycle count must be 0.
    check_reset_next_zero: assert property (
        @(posedge clk) rst |-> ##1 (count == 16'd0)
    );

    // On reset deassertion, count must be 0 in that cycle.
    check_reset_deassert_zero_now: assert property (
        @(posedge clk) $fell(rst) |-> (count == 16'd0)
    );

    // Exact next-state function: next count = rst ? 0 : (prev==FFFF ? 0 : prev+1).
    check_next_state_function: assert property (
        @(posedge clk) 1'b1 |-> ##1 ( count == ( rst ? 16'd0 : ( ($past(count,1) == 16'hFFFF) ? 16'd0 : ($past(count,1) + 16'd1) ) ) )
    );

    // If not in reset and previous count was not max, next must be previous+1.
    check_increment_when_no_reset: assert property (
        @(posedge clk) disable iff (rst) (!rst && ($past(count,1) != 16'hFFFF)) |-> ##1 (count == $past(count,1) + 16'd1)
    );

    // If not in reset and previous count was max, next must be 0.
    check_wrap_when_no_reset: assert property (
        @(posedge clk) disable iff (rst) (!rst && ($past(count,1) == 16'hFFFF)) |-> ##1 (count == 16'd0)
    );

endmodule