module counter_sva (
    input logic clk,
    input logic rst_n,
    input logic [3:0] counter_out
);
    ///// Reset behavior /////
    // While reset is asserted (active-low), counter_out is 0.
    check_reset_forces_zero: assert property (
        @(posedge clk) (!rst_n) |-> (counter_out == 4'b0000)
    );

    // If reset was asserted in the previous cycle, the previous counter value was 0.
    check_prev_cycle_reset_value_zero: assert property (
        @(posedge clk) $past(!rst_n) |-> ($past(counter_out) == 4'b0000)
    );

    ///// Release from reset /////
    // On the first cycle after reset deasserts, counter_out becomes 1.
    check_first_value_after_reset_is_one: assert property (
        @(posedge clk) $rose(rst_n) |-> (counter_out == 4'd1)
    );

    ///// Counting step that is always safe /////
    // When not in reset and previous value was 0, the next value is 1.
    check_zero_advances_to_one: assert property (
        @(posedge clk) disable iff (!rst_n) ($past(counter_out) == 4'd0) |-> (counter_out == 4'd1)
    );
endmodule