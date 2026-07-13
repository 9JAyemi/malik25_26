module SNPS_CLOCK_GATE_HIGH_RegisterAdd_W64_0_6_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic ENCLK,
    input logic TLATNTSCAX2TS_E,
    input logic TLATNTSCAX2TS_SE,
    input logic TLATNTSCAX2TS_CK,
    input logic TLATNTSCAX2TS_ECK
);

    // ENCLK captures EN on each rising edge.
    check_enclk_captures_en: assert property (
        @(posedge CLK) 1'b1 |=> (ENCLK == $past(EN))
    );

    // ECK reflects the registered EN value.
    check_eck_captures_en: assert property (
        @(posedge CLK) 1'b1 |=> (TLATNTSCAX2TS_ECK == $past(EN))
    );

    // E is a direct copy of EN.
    check_e_mirrors_en: assert property (
        @(posedge CLK) TLATNTSCAX2TS_E == EN
    );

    // SE is a direct copy of TE.
    check_se_mirrors_te: assert property (
        @(posedge CLK) TLATNTSCAX2TS_SE == TE
    );

    // CK is a direct copy of CLK.
    check_ck_mirrors_clk: assert property (
        @(posedge CLK) TLATNTSCAX2TS_CK == CLK
    );

    // ECK is a direct copy of ENCLK.
    check_eck_mirrors_enclk: assert property (
        @(posedge CLK) TLATNTSCAX2TS_ECK == ENCLK
    );

    // EN high drives ENCLK high on the next rising edge.
    check_en_high_sets_enclk: assert property (
        @(posedge CLK) EN |=> ENCLK
    );

    // EN low drives ENCLK low on the next rising edge.
    check_en_low_clears_enclk: assert property (
        @(posedge CLK) !EN |=> !ENCLK
    );

endmodule