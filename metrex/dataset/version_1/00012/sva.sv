module SNPS_CLOCK_GATE_HIGH_RegisterAdd_W24_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic ENCLK
);
    // Analysis:
    // - Clocks: CLK (top-level). The internal TLATNTSCAX2TS uses CK which is connected to CLK.
    // - Reset: None present in the RTL.
    // - Logic type: Purely combinational. ENCLK is driven by a continuous assign: ENCLK = EN & TE & CLK.
    // - Key behavior: Output ENCLK is the logical AND of EN, TE, and CLK. When CLK=1, ENCLK = EN & TE. When CLK=0, ENCLK = 0.

    ///// Functional equivalence to gate equation /////
    // ENCLK must equal EN & TE & CLK at every rising edge (samples when CLK=1).
    check_gate_equation_posedge: assert property (
        @(posedge CLK) ENCLK == (EN & TE & CLK)
    );

    // ENCLK must equal EN & TE & CLK at every falling edge (samples when CLK=0, thus ENCLK must be 0).
    check_gate_equation_negedge: assert property (
        @(negedge CLK) ENCLK == (EN & TE & CLK)
    );

    ///// Basic implications at CLK high /////
    // When ENCLK is HIGH at posedge, EN must be HIGH (since ENCLK = EN & TE at CLK=1).
    check_output_subset_of_en_posedge: assert property (
        @(posedge CLK) ENCLK |-> EN
    );

    // When ENCLK is HIGH at posedge, TE must be HIGH (since ENCLK = EN & TE at CLK=1).
    check_output_subset_of_te_posedge: assert property (
        @(posedge CLK) ENCLK |-> TE
    );

    ///// Forced low conditions at CLK high /////
    // If EN is LOW at posedge, ENCLK must be LOW.
    check_output_low_when_en_low_posedge: assert property (
        @(posedge CLK) (!EN) |-> (ENCLK == 1'b0)
    );

    // If TE is LOW at posedge, ENCLK must be LOW.
    check_output_low_when_te_low_posedge: assert property (
        @(posedge CLK) (!TE) |-> (ENCLK == 1'b0)
    );

    ///// Forced high condition at CLK high /////
    // If both EN and TE are HIGH at posedge, ENCLK must be HIGH.
    check_output_high_when_en_te_high_posedge: assert property (
        @(posedge CLK) (EN && TE) |-> (ENCLK == 1'b1)
    );

    ///// Edge-sensitive checks on ENCLK (observed at posedge samples) /////
    // A rising transition on ENCLK between posedges can only occur if EN and TE are HIGH at the current posedge.
    check_output_rise_requires_en_te_high_posedge: assert property (
        @(posedge CLK) $rose(ENCLK) |-> (EN && TE)
    );

    // A falling transition on ENCLK between posedges can only occur if at least one of EN or TE is LOW at the current posedge.
    check_output_fall_requires_en_or_te_low_posedge: assert property (
        @(posedge CLK) $fell(ENCLK) |-> ((!EN) || (!TE))
    );

    ///// Stability under stable inputs (observed at posedge samples) /////
    // If EN and TE are stable across consecutive posedges, ENCLK must also be stable across those posedges.
    check_stability_when_en_te_stable_over_posedges: assert property (
        @(posedge CLK) ($stable(EN) && $stable(TE)) |-> $stable(ENCLK)
    );

endmodule