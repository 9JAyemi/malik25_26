module d_ff_en_gate_sva (
    input logic CLK,
    input logic D,
    input logic EN,
    input logic TE,
    input logic Q,
    input logic ENCLK
);

// ENCLK is the gated clock derived from TE.
    check_enclk_is_gated_clk: assert property (
        @(posedge CLK) ENCLK == TE
    );

// When EN is low, Q holds its previous value on the next gated clock.
    check_q_holds_when_en_low: assert property (
        @(posedge CLK) !EN |=> (Q == $past(Q))
    );

// When EN is high, Q captures D on the next gated clock.
    check_q_captures_d_when_en_high: assert property (
        @(posedge CLK) EN |=> (Q == $past(D))
    );

// When EN is high and D differs from Q, Q updates to D on the next gated clock.
    check_q_updates_on_d_change_when_en_high: assert property (
        @(posedge CLK) (EN && (D != Q)) |=> (Q == $past(D))
    );

// When EN is high and D equals Q, Q remains unchanged on the next gated clock.
    check_q_stable_when_en_high_and_d_equals_q: assert property (
        @(posedge CLK) (EN && (D == Q)) |=> (Q == $past(Q))
    );

endmodule
