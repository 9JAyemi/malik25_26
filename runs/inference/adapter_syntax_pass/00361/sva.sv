module d_ff_en_gate_sva (
    input logic CLK,
    input logic D,
    input logic EN,
    input logic TE,
    input logic Q,
    input logic ENCLK
);

    // ENCLK is the gated clock derived from TE.
    check_enclk_matches_te: assert property (
        @(posedge CLK) disable iff (1'b0)
        ENCLK == TE
    );

    // ENCLK is high on the first clock after TE is high.
    check_enclk_rises_on_te_rise: assert property (
        @(posedge CLK) disable iff (1'b0)
        $rose(TE) |-> ENCLK
    );

    // ENCLK is low on the first clock after TE is low.
    check_enclk_falls_on_te_fall: assert property (
        @(posedge CLK) disable iff (1'b0)
        $fell(TE) |-> !ENCLK
    );

    // ENCLK stays high while TE stays high.
    check_enclk_holds_when_te_high: assert property (
        @(posedge CLK) disable iff (1'b0)
        (TE && $past(TE)) |-> ENCLK
    );

    // ENCLK stays low while TE stays low.
    check_enclk_holds_when_te_low: assert property (
        @(posedge CLK) disable iff (1'b0)
        (!TE && !$past(TE)) |-> !ENCLK
    );

    // Q captures D on the first clock after EN is high.
    check_q_captures_d_on_en_rise: assert property (
        @(posedge CLK) disable iff (1'b0)
        $rose(EN) |-> ##1 (Q == $past(D))
    );

    // Q holds its value on the first clock after EN is low.
    check_q_holds_on_en_fall: assert property (
        @(posedge CLK) disable iff (1'b0)
        $fell(EN) |-> ##1 (Q == $past(Q))
    );

    // Q matches D on the first clock after ENCLK is high.
    check_q_captures_d_on_enclk_rise: assert property (
        @(posedge CLK) disable iff (1'b0)
        $rose(ENCLK) |-> ##1 (Q == $past(D))
    );

    // Q holds its value on the first clock after ENCLK is low.
    check_q_holds_on_enclk_fall: assert property (
        @(posedge CLK) disable iff (1'b0)
        $fell(ENCLK) |-> ##1 (Q == $past(Q))
    );

endmodule