module binary_counter_sva (
    input logic       clk,
    input logic       reset,
    input logic [7:0] count
);

    // A sampled low reset forces count to zero by the next sampled cycle.
    check_reset_clears_by_next_cycle: assert property (
        @(posedge clk) disable iff ($initstate)
        !reset |=> (count == 8'h00)
    );

    // The first sampled cycle after reset release still has count at zero.
    check_release_from_reset_starts_at_zero: assert property (
        @(posedge clk) disable iff (!reset || $initstate)
        !$past(reset) |-> (count == 8'h00)
    );

    // Any nonzero sampled count value comes from incrementing the prior value.
    check_nonzero_values_come_from_increment: assert property (
        @(posedge clk) disable iff (!reset || $initstate)
        ($past(reset) && (count != 8'h00)) |-> (count == ($past(count) + 8'd1))
    );

    // A sampled 8'hFF count wraps to zero on the next sampled cycle.
    check_ff_wraps_to_zero: assert property (
        @(posedge clk) disable iff (!reset || $initstate)
        ($past(reset) && ($past(count) == 8'hFF)) |-> (count == 8'h00)
    );

endmodule