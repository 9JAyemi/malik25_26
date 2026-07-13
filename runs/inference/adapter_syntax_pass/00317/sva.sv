module SNPS_CLOCK_GATE_HIGH_RegisterAdd_W32_1_1_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic ENCLK
);

    // ENCLK is high on the first clock after TE is high.
    check_enclk_rises_after_te_rise: assert property (
        @(posedge CLK) disable iff ($initstate)
        $rose(TE) |-> ##1 ENCLK
    );

    // ENCLK is low on the first clock after TE is low.
    check_enclk_falls_after_te_fall: assert property (
        @(posedge CLK) disable iff ($initstate)
        $fell(TE) |-> !ENCLK
    );

    // ENCLK is high on the first clock after EN is high.
    check_enclk_rises_after_en_rise: assert property (
        @(posedge CLK) disable iff ($initstate)
        $rose(EN) |-> ##1 ENCLK
    );

    // ENCLK is low on the first clock after EN is low.
    check_enclk_falls_after_en_fall: assert property (
        @(posedge CLK) disable iff ($initstate)
        $fell(EN) |-> !ENCLK
    );

    // ENCLK is high on the first clock after ENCLK is high.
    check_enclk_rises_after_enclk_rise: assert property (
        @(posedge CLK) disable iff ($initstate)
        $rose(ENCLK) |-> ##1 ENCLK
    );

    // ENCLK is low on the first clock after ENCLK is low.
    check_enclk_falls_after_enclk_fall: assert property (
        @(posedge CLK) disable iff ($initstate)
        $fell(ENCLK) |-> !ENCLK
    );

endmodule