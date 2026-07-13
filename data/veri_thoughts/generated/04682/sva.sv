module flag_domain_crossing_ce_sva (
    input logic       CLK_A,
    input logic       CLK_A_CE,
    input logic       CLK_B,
    input logic       CLK_B_CE,
    input logic       FLAG_IN_CLK_A,
    input logic       FLAG_OUT_CLK_B,
    input logic       FLAG_TOGGLE_CLK_A,
    input logic [2:0] SYNC_CLK_B
);

    // Enabled CLK_A cycles XOR FLAG_IN into the toggle bit.
    check_toggle_update_when_ce_high: assert property (
        @(posedge CLK_A)
        CLK_A_CE |=> FLAG_TOGGLE_CLK_A === ($past(FLAG_TOGGLE_CLK_A) ^ $past(FLAG_IN_CLK_A))
    );

    // Disabled CLK_A cycles leave the toggle bit unchanged.
    check_toggle_hold_when_ce_low: assert property (
        @(posedge CLK_A)
        !CLK_A_CE |=> FLAG_TOGGLE_CLK_A === $past(FLAG_TOGGLE_CLK_A)
    );

    // Enabled CLK_B cycles shift in the sampled toggle bit.
    check_sync_shift_when_ce_high: assert property (
        @(posedge CLK_B)
        CLK_B_CE |=> SYNC_CLK_B === { $past(SYNC_CLK_B[1:0]), $past(FLAG_TOGGLE_CLK_A) }
    );

    // Disabled CLK_B cycles leave the synchronizer unchanged.
    check_sync_hold_when_ce_low: assert property (
        @(posedge CLK_B)
        !CLK_B_CE |=> SYNC_CLK_B === $past(SYNC_CLK_B)
    );

    // FLAG_OUT_CLK_B is the XOR of the top two synchronizer stages.
    check_flag_out_is_xor: assert property (
        @(posedge CLK_B)
        FLAG_OUT_CLK_B === (SYNC_CLK_B[2] ^ SYNC_CLK_B[1])
    );

    // After an enabled CLK_B shift, FLAG_OUT reflects the prior lower two stages.
    check_flag_out_updates_from_prior_sync_stages: assert property (
        @(posedge CLK_B)
        CLK_B_CE |=> FLAG_OUT_CLK_B === ($past(SYNC_CLK_B[1]) ^ $past(SYNC_CLK_B[0]))
    );

    // Without CLK_B_CE, FLAG_OUT_CLK_B remains unchanged.
    check_flag_out_holds_when_ce_low: assert property (
        @(posedge CLK_B)
        !CLK_B_CE |=> FLAG_OUT_CLK_B === $past(FLAG_OUT_CLK_B)
    );

endmodule