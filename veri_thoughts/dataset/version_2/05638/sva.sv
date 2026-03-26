module binary_counter_sva (
    input logic clk,
    input logic rst,
    input logic test_mode,
    input logic up,
    input logic down,
    input logic [3:0] count
);

    // Active-low reset forces the count to zero.
    check_reset_clears_count: assert property (
        @(posedge clk) !rst |-> (count == 4'h0)
    );

    // Normal mode increments every cycle with wraparound.
    check_normal_mode_increment: assert property (
        @(posedge clk) disable iff (!rst)
        (!test_mode) |=> (count == (($past(count) == 4'hF) ? 4'h0 : ($past(count) + 4'd1)))
    );

    // In test mode, up increments the count and has priority over down.
    check_test_mode_up_increment: assert property (
        @(posedge clk) disable iff (!rst)
        (test_mode && up) |=> (count == (($past(count) == 4'hF) ? 4'h0 : ($past(count) + 4'd1)))
    );

    // In test mode, down decrements the count when up is not asserted.
    check_test_mode_down_decrement: assert property (
        @(posedge clk) disable iff (!rst)
        (test_mode && !up && down) |=> (count == (($past(count) == 4'h0) ? 4'hF : ($past(count) - 4'd1)))
    );

    // In test mode with no direction request, the count holds.
    check_test_mode_idle_hold: assert property (
        @(posedge clk) disable iff (!rst)
        (test_mode && !up && !down) |=> (count == $past(count))
    );

endmodule