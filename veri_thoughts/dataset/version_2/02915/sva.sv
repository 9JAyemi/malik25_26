module up_counter_4bit_async_reset_sva (
    input logic clk,
    input logic rst,          // active-low async reset
    input logic [3:0] q
);

    // When reset is asserted (low) at a clock edge, q must be zero.
    reset_forces_zero: assert property (
        @(posedge clk) (!rst) |-> (q == 4'd0)
    );

    // On reset deassertion ($rose of rst), q becomes 1 (increment from 0).
    deassertion_sets_one: assert property (
        @(posedge clk) $rose(rst) |-> (q == 4'd1)
    );

    // In non-reset, if q is 0 now, it must have wrapped from 15 last cycle.
    nonreset_zero_implies_wrap: assert property (
        @(posedge clk) disable iff (!rst) ($past(1'b1) && (q == 4'd0)) |-> ($past(rst) && ($past(q) == 4'd15))
    );

    // In non-reset, if q is 2..15 now, last q must be q-1.
    nonreset_mid_values_step: assert property (
        @(posedge clk) disable iff (!rst) ($past(1'b1) && (q inside {[4'd2:4'd15]})) |-> ($past(rst) && ($past(q) == (q - 4'd1)))
    );

    // In non-reset, if last q was 0, current q must be 1.
    nonreset_prev_zero_to_one: assert property (
        @(posedge clk) disable iff (!rst) ($past(1'b1) && $past(rst) && ($past(q) == 4'd0)) |-> (q == 4'd1)
    );

    // In non-reset, if last q was 15, current q is either 0 (wrap) or 1 (if async reset glitched between edges).
    nonreset_prev_fifteen_results_0_or_1: assert property (
        @(posedge clk) disable iff (!rst) ($past(1'b1) && $past(rst) && ($past(q) == 4'd15)) |-> (q inside {4'd0, 4'd1})
    );

endmodule