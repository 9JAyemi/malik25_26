module TLATNTSCAX2TS_sva (
    input logic E,
    input logic SE,
    input logic CK,
    input logic ECK
);

    // ECK must match the RTL combinational equation.
    check_eck_matches_rtl_equation: assert property (
        @($global_clock) ECK == ((E & SE) | ((!E) & CK))
    );

    // When E is high, ECK must follow SE.
    check_eck_follows_se_when_e_high: assert property (
        @($global_clock) E |-> (ECK == SE)
    );

    // When E is low, ECK must follow CK.
    check_eck_follows_ck_when_e_low: assert property (
        @($global_clock) !E |-> (ECK == CK)
    );

    // When SE is high, ECK must be high.
    check_eck_high_when_se_high: assert property (
        @($global_clock) SE |-> ECK
    );

    // When SE is low, ECK must equal CK.
    check_eck_equals_ck_when_se_low: assert property (
        @($global_clock) !SE |-> (ECK == CK)
    );

endmodule