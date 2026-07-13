module top_module_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic out_always_ff
);
    // Output equals a&b from previous cycle.
    check_ff_is_delayed_and: assert property (
        @(posedge clk) !$isunknown($past({a,b})) |-> (out_always_ff == $past(a & b))
    );

    // If previous a&b was 1, output is 1.
    check_prev_and_high_implies_out_high: assert property (
        @(posedge clk) (!$isunknown($past({a,b})) && $past(a & b)) |-> (out_always_ff == 1'b1)
    );

    // If previous a&b was 0, output is 0.
    check_prev_and_low_implies_out_low: assert property (
        @(posedge clk) (!$isunknown($past({a,b})) && !$past(a & b)) |-> (out_always_ff == 1'b0)
    );

    // If output is 1, previous a&b must have been 1.
    check_out_high_implies_prev_and_high: assert property (
        @(posedge clk) (!$isunknown($past({a,b})) && (out_always_ff == 1'b1)) |-> ($past(a & b) == 1'b1)
    );

    // If output is 0, previous a&b must have been 0.
    check_out_low_implies_prev_and_low: assert property (
        @(posedge clk) (!$isunknown($past({a,b})) && (out_always_ff == 1'b0)) |-> ($past(a & b) == 1'b0)
    );

    // If output toggled, previous a&b must have toggled one cycle earlier.
    check_output_toggle_implies_prev_and_toggle: assert property (
        @(posedge clk)
            (!$isunknown($past({a,b})) && !$isunknown($past({a,b},2)) && !$isunknown($past(out_always_ff)) &&
             (out_always_ff != $past(out_always_ff)))
            |-> ($past(a & b) != $past(a & b, 2))
    );

    // If previous a&b toggled, output must toggle this cycle.
    check_prev_and_toggle_implies_output_toggle: assert property (
        @(posedge clk)
            (!$isunknown($past({a,b})) && !$isunknown($past({a,b},2)) && !$isunknown($past(out_always_ff)) &&
             ($past(a & b) != $past(a & b, 2)))
            |-> (out_always_ff != $past(out_always_ff))
    );

    // Output rising implies previous a&b rose (0->1) one cycle earlier.
    check_out_rise_maps_to_prev_and_rise: assert property (
        @(posedge clk)
            (!$isunknown($past({a,b})) && !$isunknown($past({a,b},2)) && !$isunknown($past(out_always_ff)) && $rose(out_always_ff))
            |-> (($past(a & b) == 1'b1) && ($past(a & b, 2) == 1'b0))
    );

    // Output falling implies previous a&b fell (1->0) one cycle earlier.
    check_out_fall_maps_to_prev_and_fall: assert property (
        @(posedge clk)
            (!$isunknown($past({a,b})) && !$isunknown($past({a,b},2)) && !$isunknown($past(out_always_ff)) && $fell(out_always_ff))
            |-> (($past(a & b) == 1'b0) && ($past(a & b, 2) == 1'b1))
    );

    // If a&b was stable over the last two cycles, output is stable over the last cycle.
    check_output_stability_when_prev_and_stable: assert property (
        @(posedge clk)
            (!$isunknown($past({a,b})) && !$isunknown($past({a,b},2)) && !$isunknown($past(out_always_ff)) &&
             ($past(a & b) == $past(a & b, 2)))
            |-> (out_always_ff == $past(out_always_ff))
    );
endmodule