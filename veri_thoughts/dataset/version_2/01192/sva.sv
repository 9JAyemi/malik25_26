module binary_counter_sva (
    input logic reset,
    input logic clk,
    input logic [3:0] count_out
);

    ///// Reset behavior /////
    // While reset is asserted low, the counter output must be 0.
    reset_forces_zero: assert property (
        @(posedge clk) !reset |-> (count_out == 4'd0)
    );

    // If reset stays asserted across cycles, the counter output stays 0.
    reset_holds_zero: assert property (
        @(posedge clk) (!reset && $past(!reset)) |-> (count_out == 4'd0 && $past(count_out) == 4'd0)
    );

    // On reset deassertion, output is 0 in that cycle and 1 in the next.
    reset_release_sequence: assert property (
        @(posedge clk) disable iff (!reset) $rose(reset) |-> (count_out == 4'd0) ##1 (count_out == 4'd1)
    );

    ///// Counting behavior /////
    // When active and not at 15, next value increments by 1.
    count_increments_when_not_max: assert property (
        @(posedge clk) disable iff (!reset) (count_out != 4'hF) |-> ##1 (count_out == $past(count_out) + 4'd1)
    );

    // When active and at 15, next value wraps to 0.
    count_wraps_from_max: assert property (
        @(posedge clk) disable iff (!reset) (count_out == 4'hF) |-> ##1 (count_out == 4'd0)
    );

    // On every active cycle, next value is either +1 or a wrap from 15 to 0.
    count_step_or_wrap_only: assert property (
        @(posedge clk) disable iff (!reset) 1'b1 |-> ##1 (
            (count_out == $past(count_out) + 4'd1) ||
            (($past(count_out) == 4'hF) && (count_out == 4'd0))
        )
    );

    // Starting from 0 (active), the counter returns to 0 after exactly 16 cycles.
    periodicity_16_cycles: assert property (
        @(posedge clk) disable iff (!reset) (count_out == 4'd0) |-> ##16 (count_out == 4'd0)
    );

    // From 14, the next two values are 15 then 0 (active).
    seq_14_15_0: assert property (
        @(posedge clk) disable iff (!reset) (count_out == 4'd14) |-> ##1 (count_out == 4'd15) ##1 (count_out == 4'd0)
    );

endmodule