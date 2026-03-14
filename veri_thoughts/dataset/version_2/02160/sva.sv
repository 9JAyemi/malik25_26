module gated_d_ff_en_W32_0_0_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic [31:0] D,
    input logic [31:0] Q,
    input logic gated_clk
);
    // TE=1 prevents Q updates at CLK edges.
    te_freezes_output: assert property (
        @(posedge CLK) TE |-> $stable(Q)
    );

    // EN=0 prevents Q updates at CLK edges.
    en_low_holds_output: assert property (
        @(posedge CLK) (EN == 1'b0) |-> $stable(Q)
    );

    // Rising gated_clk implies prior cycle EN=1 and TE=0.
    gated_rise_requires_en_and_not_te: assert property (
        @(posedge CLK) $rose(gated_clk) |-> ($past(EN) && !$past(TE))
    );

    // Falling gated_clk implies prior cycle TE=1.
    gated_fall_requires_te: assert property (
        @(posedge CLK) $fell(gated_clk) |-> $past(TE)
    );

    // EN=1 and TE=0 drives gated_clk HIGH in the next cycle.
    en_sets_gated_high_next: assert property (
        @(posedge CLK) (EN && !TE) |-> ##1 (gated_clk == 1'b1)
    );

    // TE=1 drives gated_clk LOW in the next cycle.
    te_sets_gated_low_next: assert property (
        @(posedge CLK) TE |-> ##1 (gated_clk == 1'b0)
    );

    // With EN=0 and TE=0, gated_clk holds its previous value.
    gated_holds_without_control: assert property (
        @(posedge CLK) (!EN && !TE) |-> (gated_clk == $past(gated_clk))
    );

    // A posedge of gated_clk can only occur when EN=1.
    gated_edge_requires_en: assert property (
        @(posedge gated_clk) EN
    );

    // A posedge of gated_clk can only occur when TE=0.
    gated_edge_requires_te_low: assert property (
        @(posedge gated_clk) !TE
    );

    // On a detected gated_clk rise, Q equals D from the prior CLK.
    q_follows_D_on_gated_rise: assert property (
        @(posedge CLK) $rose(gated_clk) |-> (Q == $past(D))
    );

endmodule