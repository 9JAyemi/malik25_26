module clock_gate_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic ENCLK
);
    // Clock: CLK; No reset in RTL. Sequential register update on CLK posedge.

    // ENCLK equals TE when EN was 1, else 0 (full functional relation to prior cycle).
    check_full_update: assert property (
        @(posedge CLK) disable iff ($initstate)
            ENCLK == ($past(EN) ? $past(TE) : 1'b0)
    );

    // When EN was 1, ENCLK equals prior TE.
    check_enabled_transfer: assert property (
        @(posedge CLK) disable iff ($initstate)
            $past(EN) |-> (ENCLK == $past(TE))
    );

    // When EN was 0, ENCLK is forced low.
    check_disabled_forces_low: assert property (
        @(posedge CLK) disable iff ($initstate)
            !$past(EN) |-> (ENCLK == 1'b0)
    );

    // ENCLK high only if both EN and TE were high in the prior cycle.
    check_high_implies_prev_en_te: assert property (
        @(posedge CLK) disable iff ($initstate)
            (ENCLK == 1'b1) |-> ($past(EN) && $past(TE))
    );

    // ENCLK low implies at least one of EN or TE was low in the prior cycle.
    check_low_implies_prev_not_both_high: assert property (
        @(posedge CLK) disable iff ($initstate)
            (ENCLK == 1'b0) |-> (!$past(EN) || !$past(TE))
    );

endmodule