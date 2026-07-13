module clock_gate_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic ENCLK,
    input logic gated_clk
);

    // gated_clk follows the previous cycle's EN && !TE decision.
    check_gated_clk_next_state: assert property (
        @(posedge CLK)
        1'b1 |=> (gated_clk === (($past(EN) === 1'b1) && ($past(TE) === 1'b0)))
    );

    // EN high with TE low sets gated_clk on the next sampled cycle.
    check_gate_sets_when_enabled: assert property (
        @(posedge CLK)
        ((EN === 1'b1) && (TE === 1'b0)) |=> (gated_clk === 1'b1)
    );

    // TE high forces gated_clk low on the next sampled cycle.
    check_te_forces_gate_low: assert property (
        @(posedge CLK)
        (TE === 1'b1) |=> (gated_clk === 1'b0)
    );

    // EN low forces gated_clk low on the next sampled cycle.
    check_en_low_forces_gate_low: assert property (
        @(posedge CLK)
        (EN === 1'b0) |=> (gated_clk === 1'b0)
    );

    // ENCLK is low at each rising-edge sample.
    check_enclk_low_on_posedge: assert property (
        @(posedge CLK)
        (ENCLK === 1'b0)
    );

    // ENCLK matches gated_clk while CLK is high.
    check_enclk_matches_gate_on_negedge: assert property (
        @(negedge CLK)
        (ENCLK === gated_clk)
    );

endmodule