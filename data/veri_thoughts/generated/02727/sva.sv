module Interleaver_sva (
    input logic clk,
    input logic trigger,
    input logic Interleave_b,
    input logic FF_en,
    input logic output_en
);

    // When trigger is LOW, output_en holds its value to next cycle.
    hold_when_no_trigger: assert property (
        @(posedge clk) !trigger |=> output_en == $past(output_en)
    );

    // On trigger with FF_en delayed 2 cycles LOW, next output_en is 0.
    set0_on_trigger_no_ff_delayed: assert property (
        @(posedge clk) (trigger && !$past(FF_en,2)) |=> (output_en == 1'b0)
    );

    // On trigger with FF_en delayed 2 cycles HIGH and Interleave delayed 2 cycles LOW, next output_en is 1.
    set1_on_trigger_ff_delayed_interleave0: assert property (
        @(posedge clk) (trigger && $past(FF_en,2) && !$past(Interleave_b,2)) |=> (output_en == 1'b1)
    );

    // On trigger with FF_en and Interleave both delayed 2 cycles HIGH, next output_en toggles.
    toggle_on_trigger_ff_delayed_interleave1: assert property (
        @(posedge clk) (trigger && $past(FF_en,2) && $past(Interleave_b,2)) |=> (output_en == !$past(output_en))
    );

    // Directional toggle: with trigger, ff delayed=1, interleave delayed=1, if prev output_en=1 then next is 0.
    toggle_dir_high_to_low: assert property (
        @(posedge clk) (trigger && $past(FF_en,2) && $past(Interleave_b,2) && $past(output_en)) |=> (output_en == 1'b0)
    );

    // Directional toggle: with trigger, ff delayed=1, interleave delayed=1, if prev output_en=0 then next is 1.
    toggle_dir_low_to_high: assert property (
        @(posedge clk) (trigger && $past(FF_en,2) && $past(Interleave_b,2) && !$past(output_en)) |=> (output_en == 1'b1)
    );

    // Any change of output_en implies trigger was HIGH in the previous cycle.
    change_only_on_trigger: assert property (
        @(posedge clk) $changed(output_en) |-> $past(trigger)
    );

    // A rising edge on output_en implies prior trigger and FF_en delayed 2 cycles HIGH.
    rise_implies_trigger_and_ff_delayed: assert property (
        @(posedge clk) $rose(output_en) |-> ($past(trigger) && $past(FF_en,2))
    );

    // A falling edge on output_en implies prior trigger was HIGH.
    fall_implies_trigger: assert property (
        @(posedge clk) $fell(output_en) |-> $past(trigger)
    );

    // Full-case next-state function for output_en on trigger (encodes the RTL ternary behavior).
    next_state_on_trigger_matches_rtl: assert property (
        @(posedge clk)
            trigger |=> (
                $past(FF_en,2)
                    ? ( $past(Interleave_b,2) ? (output_en == !$past(output_en)) : (output_en == 1'b1) )
                    : (output_en == 1'b0)
            )
    );

endmodule