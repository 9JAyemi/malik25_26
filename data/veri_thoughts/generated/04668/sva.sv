module binary_counter_sva (
    input logic       clk,
    input logic       reset,
    input logic [3:0] count
);

    // Single-clock sequential counter with active-high synchronous reset.

    // A reset seen on the prior clock forces count to zero.
    check_reset_clears_count: assert property (
        @(posedge clk) disable iff ($initstate)
        $past(reset) |-> (count == 4'b0000)
    );

    // Outside reset, count follows the RTL next-state relation.
    check_count_next_state: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        (count == ($past(reset) ? 4'b0000 : ($past(count) + 4'd1)))
    );

    // Outside reset, 4'hF wraps to 4'h0 on the next cycle.
    check_count_wraps: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        (!$past(reset) && ($past(count) == 4'hF)) |-> (count == 4'h0)
    );

endmodule