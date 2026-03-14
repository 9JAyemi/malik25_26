module tlatntscax2ts_sva (
    input logic E,
    input logic SE,
    input logic CK,
    input logic ECK
);
    // ECK must equal E & SE & CK.
    check_eck_equivalence: assert property (
        @(posedge CK) ECK == (E & SE & CK)
    );

    // ECK can be HIGH only if E, SE, and CK are HIGH.
    check_eck_high_implies_inputs_high: assert property (
        @(posedge CK) (ECK == 1'b1) |-> (E && SE && CK)
    );

    // If E or SE is LOW, ECK must be LOW.
    check_eck_low_when_any_enable_low: assert property (
        @(posedge CK) ((!E) || (!SE)) |-> (ECK == 1'b0)
    );

    // Rising edge on ECK requires all inputs HIGH.
    check_eck_rise_requires_all_high: assert property (
        @(posedge CK) $rose(ECK) |-> (E && SE && CK)
    );

    // Falling edge on ECK implies at least one input is LOW.
    check_eck_fall_implies_some_low: assert property (
        @(posedge CK) $fell(ECK) |-> ((!E) || (!SE) || (!CK))
    );

    // If E, SE, and CK are stable between samples, ECK must be stable.
    check_eck_stable_when_inputs_stable: assert property (
        @(posedge CK) ($stable(E) && $stable(SE) && $stable(CK)) |-> $stable(ECK)
    );

    // When both enables are HIGH, ECK must track CK.
    check_eck_tracks_ck_when_enabled: assert property (
        @(posedge CK) (E && SE) |-> (ECK == CK)
    );

    // With stable LOW enables, ECK must remain LOW across samples.
    check_eck_stays_low_when_disabled_stable: assert property (
        @(posedge CK) (((!E) || (!SE)) && $stable(E) && $stable(SE)) |-> ($stable(ECK) && (ECK == 1'b0))
    );
endmodule