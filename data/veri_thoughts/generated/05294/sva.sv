module AregLSBLog_sva (
    input logic [1:0] AregSticky,
    input logic [1:0] AregLSBSN,
    input logic [1:0] AregLSBDB,
    input logic       AregFPMSBP1,
    input logic       SNnotDB,
    input logic       TrueIEEEAregLSB,
    input logic       StickyForSR1
);

    // StickyForSR1 is the OR of the two sticky bits.
    check_sticky_or: assert property (
        @($global_clock)
        StickyForSR1 == (AregSticky[1] || AregSticky[0])
    );

    // TrueIEEEAregLSB is the selected LSB based on SNnotDB.
    check_true_lsb_mux: assert property (
        @($global_clock)
        TrueIEEEAregLSB == (SNnotDB ? AregLSBSN[0] : AregLSBDB[0])
    );

    // In single-length mode, the single-length LSB drives the output.
    check_true_lsb_single_mode: assert property (
        @($global_clock)
        SNnotDB |-> (TrueIEEEAregLSB == AregLSBSN[0])
    );

    // In double-length mode, the double-length LSB drives the output.
    check_true_lsb_double_mode: assert property (
        @($global_clock)
        !SNnotDB |-> (TrueIEEEAregLSB == AregLSBDB[0])
    );

    // AregFPMSBP1 does not affect either output.
    check_fpmsbp1_has_no_effect: assert property (
        @($global_clock)
        !$initstate &&
        $changed(AregFPMSBP1) &&
        $stable({AregSticky, AregLSBSN, AregLSBDB, SNnotDB})
        |-> $stable({TrueIEEEAregLSB, StickyForSR1})
    );

endmodule