module clock_gate_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic ENCLK
);

    // EN high causes the registered output to be high by the next sampled cycle.
    check_en_sets_output_high: assert property (
        @(posedge CLK) EN |=> (ENCLK == 1'b1)
    );

    // EN low means the register is not updated, so the output holds its value.
    check_output_holds_when_disabled: assert property (
        @(posedge CLK) !EN |=> $stable(ENCLK)
    );

    // TE alone does not update the output when EN is low.
    check_te_has_no_effect_without_en: assert property (
        @(posedge CLK) (TE && !EN) |=> $stable(ENCLK)
    );

    // Any output rise must come from EN being high on the previous clock edge.
    check_rise_requires_prior_enable: assert property (
        @(posedge CLK) $rose(ENCLK) |-> $past(EN)
    );

    // Once the output is high, the RTL has no path that can drive it low.
    check_output_stays_high_once_set: assert property (
        @(posedge CLK) (ENCLK == 1'b1) |=> (ENCLK == 1'b1)
    );

endmodule