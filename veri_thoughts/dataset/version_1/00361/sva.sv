module DFFE_sva (
    input logic CLK,
    input logic D,
    input logic EN,
    input logic Q
);

    // Q captures D on an enabled clock edge.
    check_q_captures_d_when_enabled: assert property (
        @(posedge CLK) EN |=> (Q == $past(D))
    );

    // Q holds its value when EN is low.
    check_q_holds_when_disabled: assert property (
        @(posedge CLK) !EN |=> (Q == $past(Q))
    );

endmodule

module d_ff_en_gate_sva (
    input logic CLK,
    input logic D,
    input logic EN,
    input logic TE,
    input logic Q,
    input logic ENCLK
);

    // ENCLK is driven high after a clock edge with TE and EN high.
    check_enclk_sets_when_te_and_en_high: assert property (
        @(posedge CLK) (TE && EN) |=> ENCLK
    );

    // ENCLK is driven low after a clock edge with TE high and EN low.
    check_enclk_clears_when_te_high_and_en_low: assert property (
        @(posedge CLK) (TE && !EN) |=> !ENCLK
    );

    // ENCLK holds its value when TE is low.
    check_enclk_holds_when_te_low: assert property (
        @(posedge CLK) !TE |=> (ENCLK == $past(ENCLK))
    );

    // Q captures D when the gated clock is caused to rise.
    check_q_captures_d_on_gated_clock_rise: assert property (
        @(posedge CLK) (TE && EN && !ENCLK) |=> (Q == $past(D))
    );

    // Q holds when the gated clock does not rise.
    check_q_holds_without_gated_clock_rise: assert property (
        @(posedge CLK) !(TE && EN && !ENCLK) |=> (Q == $past(Q))
    );

endmodule