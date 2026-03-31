module clock_gate_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic ENCLK
);
    // ENCLK equals previous-cycle TE & EN.
    check_enclk_matches_prev_te_and_en: assert property (
        @(posedge CLK) disable iff ($initstate) ENCLK == $past(TE & EN)
    );

    // When TE is LOW, ENCLK must be LOW on the next cycle.
    check_te_low_clears_enclk_next: assert property (
        @(posedge CLK) disable iff ($initstate) !TE |=> !ENCLK
    );

    // When EN is LOW, ENCLK must be LOW on the next cycle.
    check_en_low_clears_enclk_next: assert property (
        @(posedge CLK) disable iff ($initstate) !EN |=> !ENCLK
    );

    // If TE and EN are HIGH in consecutive cycles, ENCLK is HIGH in the next cycle.
    check_te_and_en_set_enclk_next: assert property (
        @(posedge CLK) disable iff ($initstate) (TE && EN) |=> ENCLK
    );

    // If ENCLK is HIGH, the previous cycle must have had TE and EN HIGH.
    check_enclk_high_requires_prev_te_and_en: assert property (
        @(posedge CLK) disable iff ($initstate) ENCLK |-> $past(TE && EN)
    );

    // If ENCLK is LOW, the previous cycle must not have had TE and EN HIGH.
    check_enclk_low_requires_prev_not_te_and_en: assert property (
        @(posedge CLK) disable iff ($initstate) !ENCLK |-> !$past(TE && EN)
    );

    // If TE and EN are HIGH in consecutive cycles, ENCLK is HIGH in the next cycle.
    check_te_and_en_set_enclk_next: assert property (
        @(posedge CLK) disable iff ($initstate) (TE && EN) |=> ENCLK
    );

    // If TE and EN are HIGH in consecutive cycles, ENCLK is HIGH in the next cycle.
    check_te_and_en_set_enclk_next: assert property (
        @(posedge CLK) disable iff ($initstate) (TE && EN) |=> ENCLK
    );

    // If TE and EN are HIGH in consecutive cycles, ENCLK is HIGH in the next cycle.
    check_te_and_en_set_enclk_next: assert property (
        @(posedge CLK) disable iff ($initstate) (TE && EN) |=> ENCLK
    );

    // If TE and EN are HIGH in consecutive cycles, ENCLK is HIGH in the next cycle.
    check_te_and_en_set_enclk_next: assert property (
        @(posedge CLK) disable iff ($initstate) (TE && EN) |=> ENCLK
    );
endmodule