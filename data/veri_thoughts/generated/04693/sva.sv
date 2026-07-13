module up_counter_assertions (
    input logic clk,
    input logic rst,
    input logic [3:0] count
);

    // Clock: clk
    // Reset: rst is active-high and asynchronous.
    // Logic: sequential 4-bit up-counter.

    // A sampled reset-high cycle forces count to zero by the next sampled clock.
    check_reset_forces_zero_next_cycle: assert property (
        @(posedge clk) disable iff ($initstate)
        rst |=> (count == 4'd0)
    );

    // Count stays zero while reset is sampled high across consecutive clocks.
    check_reset_hold_keeps_zero: assert property (
        @(posedge clk) disable iff ($initstate)
        (rst && $past(rst)) |-> (count == 4'd0)
    );

    // Any sampled nonzero count must come from a prior non-reset increment.
    check_nonzero_counts_advance_by_one: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        (count != 4'd0) |-> (!$past(rst) && (count == ($past(count) + 4'd1)))
    );

    // A sampled 15 must wrap to zero on the next sampled clock.
    check_wrap_from_max_to_zero: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        (!$past(rst) && ($past(count) == 4'hF)) |-> (count == 4'h0)
    );

endmodule