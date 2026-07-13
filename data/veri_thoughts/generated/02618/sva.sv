module latch_sva (
    input logic E,
    input logic SE,
    input logic CK,
    input logic ECK
);
    // ECK equals prior cycle's (E && !SE).
    check_eck_matches_past_enable: assert property (
        @(posedge CK) disable iff ($initstate) ECK == $past(E && !SE)
    );

    // If SE was 1 last cycle, ECK must be 0 now.
    check_eck_zero_on_se: assert property (
        @(posedge CK) disable iff ($initstate) $past(SE) |-> (ECK == 1'b0)
    );

    // If E was 1 and SE was 0 last cycle, ECK must be 1 now.
    check_eck_one_on_enable: assert property (
        @(posedge CK) disable iff ($initstate) $past(E && !SE) |-> (ECK == 1'b1)
    );

    // If E was 0 and SE was 0 last cycle, ECK must be 0 now.
    check_eck_zero_when_disabled: assert property (
        @(posedge CK) disable iff ($initstate) $past(!E && !SE) |-> (ECK == 1'b0)
    );
endmodule

module clock_gate_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic ENCLK
);
    // ENCLK equals prior cycle's (EN && !TE).
    check_enclk_matches_past_enable: assert property (
        @(posedge CLK) disable iff ($initstate) ENCLK == $past(EN && !TE)
    );

    // If TE was 1 last cycle, ENCLK must be 0 now.
    check_enclk_zero_on_te: assert property (
        @(posedge CLK) disable iff ($initstate) $past(TE) |-> (ENCLK == 1'b0)
    );

    // If EN was 1 and TE was 0 last cycle, ENCLK must be 1 now.
    check_enclk_one_on_enable: assert property (
        @(posedge CLK) disable iff ($initstate) $past(EN && !TE) |-> (ENCLK == 1'b1)
    );

    // If EN was 0 and TE was 0 last cycle, ENCLK must be 0 now.
    check_enclk_zero_when_disabled: assert property (
        @(posedge CLK) disable iff ($initstate) $past(!EN && !TE) |-> (ENCLK == 1'b0)
    );
endmodule