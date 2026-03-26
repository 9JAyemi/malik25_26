module clock_gate_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic ENCLK
);

    // ENCLK reflects the prior cycle's EN && !TE value.
    check_enclk_matches_registered_gate: assert property (
        @(posedge CLK) 1'b1 |=> (ENCLK == ($past(EN) && !$past(TE)))
    );

    // EN high with TE low makes ENCLK high on the next clock.
    check_enable_sets_enclk: assert property (
        @(posedge CLK) (EN && !TE) |=> ENCLK
    );

    // EN low or TE high makes ENCLK low on the next clock.
    check_disable_clears_enclk: assert property (
        @(posedge CLK) (!EN || TE) |=> !ENCLK
    );

endmodule