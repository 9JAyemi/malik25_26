module gated_d_ff_en_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic ENCLK,
    input logic ENCLK_reg
);

    // Output is forced low whenever enable is low.
    check_output_low_when_disabled: assert property (
        @(posedge CLK) disable iff ($initstate) !EN |-> (ENCLK === 1'b0)
    );

    // Output mirrors the stored register whenever enable is high.
    check_output_matches_reg_when_enabled: assert property (
        @(posedge CLK) disable iff ($initstate) EN |-> (ENCLK === ENCLK_reg)
    );

    // An enabled clock edge captures TE into the internal register.
    check_reg_captures_te_when_enabled: assert property (
        @(posedge CLK) disable iff ($initstate) EN |=> (ENCLK_reg === $past(TE))
    );

    // A disabled clock edge leaves the internal register unchanged.
    check_reg_holds_when_disabled: assert property (
        @(posedge CLK) disable iff ($initstate) !EN |=> (ENCLK_reg === $past(ENCLK_reg))
    );

    // With enable high in consecutive cycles, output is the prior TE sample.
    check_output_follows_prior_te_under_continuous_enable: assert property (
        @(posedge CLK) disable iff ($initstate) EN && $past(EN) |-> (ENCLK === $past(TE))
    );

endmodule

bind gated_d_ff_en gated_d_ff_en_sva gated_d_ff_en_sva_inst (
    .CLK(CLK),
    .EN(EN),
    .TE(TE),
    .ENCLK(ENCLK),
    .ENCLK_reg(ENCLK_reg)
);