module CLK_GATE_MODULE_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic ENCLK
);
    ///// Combinational clock-gating behavior, sampled on CLK posedge /////
    // When enabled and TE low, ENCLK must equal CLK.
    check_pass_through_when_enabled: assert property (
        @(posedge CLK) (EN && !TE) |-> (ENCLK == CLK)
    );
    // EN low forces ENCLK low.
    check_en_low_forces_zero: assert property (
        @(posedge CLK) (!EN) |-> (ENCLK == 1'b0)
    );
    // TE high forces ENCLK low.
    check_te_high_forces_zero: assert property (
        @(posedge CLK) (TE) |-> (ENCLK == 1'b0)
    );
    // ENCLK high implies EN is high.
    check_enclk_high_implies_en: assert property (
        @(posedge CLK) (ENCLK == 1'b1) |-> (EN == 1'b1)
    );
    // ENCLK high implies TE is low.
    check_enclk_high_implies_te_low: assert property (
        @(posedge CLK) (ENCLK == 1'b1) |-> (!TE)
    );
    // Rising EN with TE low drives ENCLK high in the same cycle.
    check_en_rise_sets_enclk_when_te_low: assert property (
        @(posedge CLK) ($rose(EN) && !TE) |-> (ENCLK == 1'b1)
    );
    // Falling EN forces ENCLK low in the same cycle.
    check_en_fall_clears_enclk: assert property (
        @(posedge CLK) $fell(EN) |-> (ENCLK == 1'b0)
    );
    // Rising TE forces ENCLK low in the same cycle.
    check_te_rise_clears_enclk: assert property (
        @(posedge CLK) $rose(TE) |-> (ENCLK == 1'b0)
    );
    // Falling TE with EN high drives ENCLK high in the same cycle.
    check_te_fall_sets_enclk_when_en_high: assert property (
        @(posedge CLK) ($fell(TE) && EN) |-> (ENCLK == 1'b1)
    );
    // If gating is off (EN low or TE high), ENCLK must be low.
    check_gating_off_forces_zero: assert property (
        @(posedge CLK) ((!EN) || TE) |-> (ENCLK == 1'b0)
    );
endmodule