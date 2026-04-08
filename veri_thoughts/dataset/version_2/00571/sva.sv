module up_counter_sva (
    input logic       clk,
    input logic       rst,
    input logic [3:0] count
);

    // Reset drives the counter to zero.
    check_reset_drives_zero: assert property (
        @(posedge clk) disable iff ($initstate && !rst)
        !rst |-> (count == 4'd0)
    );

    // The first sampled cycle after reset release still shows zero.
    check_release_keeps_zero: assert property (
        @(posedge clk) disable iff (!rst)
        (!$initstate && $rose(rst)) |-> (count == 4'd0)
    );

    // Across sampled active cycles, count either increments or is zeroed by async reset.
    check_active_transition_is_increment_or_zero: assert property (
        @(posedge clk) disable iff (!rst)
        (!$initstate && $past(rst)) |-> ((count == 4'd0) || (count == ($past(count) + 4'd1)))
    );

    // A sampled value of 15 wraps to zero on the next active clock.
    check_wraps_from_f_to_zero: assert property (
        @(posedge clk) disable iff (!rst)
        (!$initstate && $past(rst) && ($past(count) == 4'hF)) |-> (count == 4'h0)
    );

endmodule