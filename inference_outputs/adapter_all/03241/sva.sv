module clock_gate_high_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic ENCLK
);

    // TE high forces the gated clock low.
    check_te_forces_enclk_low: assert property (
        @(posedge CLK) TE |-> !ENCLK
    );

    // A sampled low EN forces the gated clock low on the next CLK edge.
    check_en_low_forces_enclk_low: assert property (
        @(posedge CLK) disable iff (TE) !EN |=> !ENCLK
    );

    // A sampled high EN forces the gated clock high on the next CLK edge.
    check_en_high_forces_enclk_high: assert property (
        @(posedge CLK) disable iff (TE) EN |=> ENCLK
    );

    // A sampled high ENCLK must come from a prior CLK edge with EN high.
    check_enclk_high_requires_prior_en_high: assert property (
        @(posedge CLK) disable iff (TE) ENCLK |-> $past(!TE && EN)
    );

    // A sampled low ENCLK must come from a prior CLK edge with EN low or TE high.
    check_enclk_low_requires_prior_en_low_or_te_high: assert property (
        @(posedge CLK) disable iff (TE) !ENCLK |-> $past((!EN) || TE)
    );

endmodule