module d_ff_en_gate_sva (
    input logic CLK,
    input logic D,
    input logic EN,
    input logic TE,
    input logic Q,
    input logic ENCLK
);
    // ENCLK is the gated clock derived from TE on CLK edges.
    check_enclk_is_gated_clk: assert property (
        @(posedge CLK) ENCLK == TE
    );

    // When TE is LOW, ENCLK is LOW on the next CLK edge.
    check_enclk_low_when_te_low: assert property (
        @(posedge CLK) !TE |=> !ENCLK
    );

    // When TE is HIGH, ENCLK is HIGH on the next CLK edge.
    check_enclk_high_when_te_high: assert property (
        @(posedge CLK) TE |=> ENCLK
    );

    // With TE HIGH, a rising EN at a CLK edge causes a rising ENCLK on the next CLK edge.
    check_en_rise_propagates_to_enclk: assert property (
        @(posedge CLK) TE && $rose(EN) |=> $rose(ENCLK)
    );

    // With TE HIGH, a falling EN at a CLK edge causes a falling ENCLK on the next CLK edge.
    check_en_fall_propagates_to_enclk: assert property (
        @(posedge CLK) TE && $fell(EN) |=> $fell(ENCLK)
    );

    // With TE HIGH, a rising D at a CLK edge causes a rising Q on the next CLK edge.
    check_d_rise_propagates_to_q: assert property (
        @(posedge CLK) TE && $rose(D) |=> $rose(Q)
    );

    // With TE HIGH, a falling D at a CLK edge causes a falling Q on the next CLK edge.
    check_d_fall_propagates_to_q: assert property (
        @(posedge CLK) TE && $fell(D) |=> $fell(Q)
    );

    // With TE HIGH, a rising Q at a CLK edge must come from a prior ENCLK edge.
    check_q_rise_requires_enclk: assert property (
        @(posedge CLK) TE && $rose(Q) |-> $past(ENCLK)
    );

    // With TE HIGH, a falling Q at a CLK edge must come from a prior ENCLK edge.
    check_q_fall_requires_enclk: assert property (
        @(posedge CLK) TE && $fell(Q) |-> $past(ENCLK)
    );

    // With TE HIGH, a rising EN at a CLK edge causes a rising Q on the next CLK edge.
    check_en_rise_propagates_to_q: assert property (
        @(posedge CLK) TE && $rose(EN) |=> $rose(Q)
    );

    // With TE HIGH, a falling EN at a CLK edge causes a falling Q on the next CLK edge.
    check_en_fall_propagates_to_q: assert property (
        @(posedge CLK) TE && $fell(EN) |=> $fell(Q)
    );
endmodule