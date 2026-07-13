module clock_gate_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic ENCLK
);

    // RTL updates on posedge CLK and posedge TE; there is no reset.

    // A high TE sampled on the prior CLK edge forces ENCLK low now.
    check_prev_te_forces_enclk_low: assert property (
        @(posedge CLK) !$initstate && $past(TE) |-> (ENCLK == 1'b0)
    );

    // A low EN sampled with TE low on the prior CLK edge forces ENCLK low now.
    check_prev_en_low_forces_enclk_low: assert property (
        @(posedge CLK) !$initstate && !$past(TE) && !$past(EN) |-> (ENCLK == 1'b0)
    );

    // A high ENCLK sample must come from a prior CLK edge with TE low.
    check_enclk_high_requires_prev_te_low: assert property (
        @(posedge CLK) !$initstate && ENCLK |-> ($past(TE) == 1'b0)
    );

    // A high ENCLK sample must come from a prior CLK edge with EN high.
    check_enclk_high_requires_prev_en_high: assert property (
        @(posedge CLK) !$initstate && ENCLK |-> ($past(EN) == 1'b1)
    );

endmodule