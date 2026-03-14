module clock_gate_64bit_reg_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic ENCLK
);
    // Clock: CLK (posedge). No reset in RTL.
    // Behavior: At each posedge, ENCLK <= (EN & ~TE).

    // EN && !TE drives ENCLK HIGH on the next clock.
    check_next_high_when_en_and_not_te: assert property (
        @(posedge CLK) disable iff ($initstate) (EN && !TE) |=> (ENCLK == 1'b1)
    );

    // TE HIGH forces ENCLK LOW on the next clock.
    check_next_low_when_te_high: assert property (
        @(posedge CLK) disable iff ($initstate) (TE) |=> (ENCLK == 1'b0)
    );

    // EN LOW forces ENCLK LOW on the next clock.
    check_next_low_when_en_low: assert property (
        @(posedge CLK) disable iff ($initstate) (!EN) |=> (ENCLK == 1'b0)
    );

    // ENCLK equals prior cycle's (EN & ~TE).
    check_matches_past_inputs: assert property (
        @(posedge CLK) disable iff ($initstate) ENCLK == ($past(EN) & ~ $past(TE))
    );

    // Rising EN with TE LOW sets ENCLK HIGH on the next clock.
    check_en_rise_effect_when_te_low: assert property (
        @(posedge CLK) disable iff ($initstate) ($rose(EN) && !TE) |=> (ENCLK == 1'b1)
    );

    // Falling EN with TE LOW sets ENCLK LOW on the next clock.
    check_en_fall_effect_when_te_low: assert property (
        @(posedge CLK) disable iff ($initstate) ($fell(EN) && !TE) |=> (ENCLK == 1'b0)
    );
endmodule