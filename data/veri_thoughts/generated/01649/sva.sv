module CLK_GEN_sva (
    input logic CLK_IN,
    input logic CLK_OUT,
    input logic [24:0] counter
);
    // Counter resets to 0 on the cycle after it was 4166.
    check_counter_resets_at_4166: assert property (
        @(posedge CLK_IN) disable iff ($initstate)
            ($past(counter) == 25'd4166) |-> (counter == 25'd0)
    );

    // Counter increments by 1 when previous value was not 4166.
    check_counter_increments_otherwise: assert property (
        @(posedge CLK_IN) disable iff ($initstate)
            ($past(counter) != 25'd4166) |-> (counter == $past(counter) + 25'd1)
    );

    // If counter is 4166 in this cycle, it becomes 0 in the next cycle.
    check_counter_4166_then_zero_next: assert property (
        @(posedge CLK_IN) disable iff ($initstate)
            (counter == 25'd4166) |=> (counter == 25'd0)
    );

    // CLK_OUT can change only on cycles following counter==4166.
    check_clkout_change_only_on_4166: assert property (
        @(posedge CLK_IN) disable iff ($initstate)
            $changed(CLK_OUT) |-> ($past(counter) == 25'd4166)
    );

    // When previous counter != 4166, CLK_OUT must not change.
    check_clkout_stable_when_not_4166: assert property (
        @(posedge CLK_IN) disable iff ($initstate)
            ($past(counter) != 25'd4166) |-> (!$changed(CLK_OUT))
    );

    // When previous counter==4166 and CLK_OUT is known, it must toggle.
    check_clkout_toggles_on_4166_when_known: assert property (
        @(posedge CLK_IN) disable iff ($initstate)
            (($past(counter) == 25'd4166) && !$isunknown(CLK_OUT) && !$isunknown($past(CLK_OUT)))
            |-> (CLK_OUT == ~$past(CLK_OUT))
    );

    // A transition to counter==0 only comes from 4166 or from max-value overflow.
    check_counter_zero_from_only_4166_or_overflow: assert property (
        @(posedge CLK_IN) disable iff ($initstate)
            (counter == 25'd0) |-> (($past(counter) == 25'd4166) || ($past(counter) == 25'd33554431))
    );

    // If previous counter was neither 4166 nor max, next counter cannot be 0.
    check_no_spurious_zero: assert property (
        @(posedge CLK_IN) disable iff ($initstate)
            (($past(counter) != 25'd4166) && ($past(counter) != 25'd33554431)) |-> (counter != 25'd0)
    );
endmodule