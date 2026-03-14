module TLATNTSCAX2TS_sva (
    input logic E,
    input logic SE,
    input logic CK,
    input logic ECK
);
    ///// Functional equivalence /////
    // ECK equals E & SE.
    check_eck_and_equation: assert property (
        @(posedge CK) ECK == (E & SE)
    );
    // If E is LOW, ECK must be LOW.
    check_eck_low_when_e_low: assert property (
        @(posedge CK) (E == 1'b0) |-> (ECK == 1'b0)
    );
    // If SE is LOW, ECK must be LOW.
    check_eck_low_when_se_low: assert property (
        @(posedge CK) (SE == 1'b0) |-> (ECK == 1'b0)
    );
    // If ECK is HIGH, both E and SE are HIGH.
    check_eck_high_implies_inputs_high: assert property (
        @(posedge CK) (ECK == 1'b1) |-> (E == 1'b1) && (SE == 1'b1)
    );
    // When E is HIGH, ECK mirrors SE.
    check_eck_equals_se_when_e_high: assert property (
        @(posedge CK) (E == 1'b1) |-> (ECK == SE)
    );
    // When SE is HIGH, ECK mirrors E.
    check_eck_equals_e_when_se_high: assert property (
        @(posedge CK) (SE == 1'b1) |-> (ECK == E)
    );
    // ECK rising edge only when both inputs are HIGH.
    check_no_false_rise_eck: assert property (
        @(posedge CK) $rose(ECK) |-> (E && SE)
    );
    // ECK falling edge only when at least one input is LOW.
    check_no_false_fall_eck: assert property (
        @(posedge CK) $fell(ECK) |-> !(E && SE)
    );
    // If E rises while SE is HIGH, ECK must rise.
    check_eck_rises_on_e_rise_with_se_high: assert property (
        @(posedge CK) ($rose(E) && (SE == 1'b1)) |-> $rose(ECK)
    );
    // If SE rises while E is HIGH, ECK must rise.
    check_eck_rises_on_se_rise_with_e_high: assert property (
        @(posedge CK) ($rose(SE) && (E == 1'b1)) |-> $rose(ECK)
    );
    // If both inputs are stable, ECK is stable.
    check_eck_stable_when_inputs_stable: assert property (
        @(posedge CK) $stable(E) && $stable(SE) |-> $stable(ECK)
    );
endmodule

module clock_gate_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic ENCLK
);
    ///// Functional equivalence /////
    // ENCLK equals EN & TE.
    check_enclk_and_equation: assert property (
        @(posedge CLK) ENCLK == (EN & TE)
    );
    // If EN is LOW, ENCLK must be LOW.
    check_enclk_low_when_en_low: assert property (
        @(posedge CLK) (EN == 1'b0) |-> (ENCLK == 1'b0)
    );
    // If TE is LOW, ENCLK must be LOW.
    check_enclk_low_when_te_low: assert property (
        @(posedge CLK) (TE == 1'b0) |-> (ENCLK == 1'b0)
    );
    // If ENCLK is HIGH, both EN and TE are HIGH.
    check_enclk_high_implies_inputs_high: assert property (
        @(posedge CLK) (ENCLK == 1'b1) |-> (EN == 1'b1) && (TE == 1'b1)
    );
    // When EN is HIGH, ENCLK mirrors TE.
    check_enclk_equals_te_when_en_high: assert property (
        @(posedge CLK) (EN == 1'b1) |-> (ENCLK == TE)
    );
    // When TE is HIGH, ENCLK mirrors EN.
    check_enclk_equals_en_when_te_high: assert property (
        @(posedge CLK) (TE == 1'b1) |-> (ENCLK == EN)
    );
    // ENCLK rising edge only when both inputs are HIGH.
    check_no_false_rise_enclk: assert property (
        @(posedge CLK) $rose(ENCLK) |-> (EN && TE)
    );
    // ENCLK falling edge only when at least one input is LOW.
    check_no_false_fall_enclk: assert property (
        @(posedge CLK) $fell(ENCLK) |-> !(EN && TE)
    );
    // If EN rises while TE is HIGH, ENCLK must rise.
    check_enclk_rises_on_en_rise_with_te_high: assert property (
        @(posedge CLK) ($rose(EN) && (TE == 1'b1)) |-> $rose(ENCLK)
    );
    // If TE rises while EN is HIGH, ENCLK must rise.
    check_enclk_rises_on_te_rise_with_en_high: assert property (
        @(posedge CLK) ($rose(TE) && (EN == 1'b1)) |-> $rose(ENCLK)
    );
    // If both inputs are stable, ENCLK is stable.
    check_enclk_stable_when_inputs_stable: assert property (
        @(posedge CLK) $stable(EN) && $stable(TE) |-> $stable(ENCLK)
    );
endmodule