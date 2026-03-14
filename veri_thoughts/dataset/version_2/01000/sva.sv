module pipeline_register_sva #(
    parameter width = 8
)(
    input logic clk,
    input logic reset,
    input logic [width-1:0] data_in,
    input logic [width-1:0] data_out
);

    // Synchronous reset drives data_out to zero on the next clock.
    check_reset_clears_next: assert property (
        @(posedge clk) reset |=> (data_out == '0)
    );

    // While reset remains asserted, data_out is held at zero.
    check_hold_zero_during_continuous_reset: assert property (
        @(posedge clk) (reset && $past(reset)) |-> (data_out == '0)
    );

    // On the cycle reset deasserts, data_out is still zero (from prior reset cycle).
    check_zero_on_reset_fall_cycle: assert property (
        @(posedge clk) $fell(reset) |-> (data_out == '0)
    );

    // When previous cycle was not in reset, output equals previous input.
    check_capture_when_prev_not_reset: assert property (
        @(posedge clk) disable iff (reset) !$past(reset) |-> (data_out == $past(data_in))
    );

    // One cycle after reset deasserts, output captures input from the deassert cycle.
    check_capture_after_reset_deassert: assert property (
        @(posedge clk) $fell(reset) |=> (data_out == $past(data_in))
    );

    // On reset assertion edge, current output shows the previous cycle's input.
    check_prev_input_visible_on_reset_rise: assert property (
        @(posedge clk) $rose(reset) |-> (data_out == $past(data_in))
    );

    // If input was stable over two non-reset cycles, output does not change.
    check_out_stable_when_in_stable_no_reset: assert property (
        @(posedge clk) disable iff (reset)
            (!$past(reset) && !$past(reset,2) && ($past(data_in) == $past(data_in,2))) |-> (data_out == $past(data_out))
    );

endmodule