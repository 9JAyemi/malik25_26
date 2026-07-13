module clock_gate_module_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic reset,
    input logic ENCLK
);

    // A sampled reset must leave ENCLK low on the following clock.
    check_reset_clears_next_cycle: assert property (
        @(posedge CLK) reset |=> (ENCLK == 1'b0)
    );

    // From a high state, full enable must toggle ENCLK low by the next sample.
    check_toggle_high_to_low_when_enabled: assert property (
        @(posedge CLK) disable iff (reset)
        (EN && TE && ENCLK) |=> (ENCLK == 1'b0)
    );

    // From a low state, missing either enable keeps ENCLK low.
    check_low_holds_without_full_enable: assert property (
        @(posedge CLK) disable iff (reset)
        ((!EN || !TE) && !ENCLK) |=> (ENCLK == 1'b0)
    );

    // Without full enable, ENCLK cannot rise by the next sampled clock.
    check_no_rise_without_full_enable: assert property (
        @(posedge CLK) disable iff (reset)
        (!EN || !TE) |=> !$rose(ENCLK)
    );

    // A sampled rise must come from a prior low state with both enables high.
    check_rise_has_valid_cause: assert property (
        @(posedge CLK) disable iff (reset)
        $rose(ENCLK) |-> (!$past(reset) && $past(EN) && $past(TE) && !$past(ENCLK))
    );

endmodule