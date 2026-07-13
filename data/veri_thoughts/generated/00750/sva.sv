module flag_cdc_sva (
    input logic clkA,
    input logic FlagIn_clkA,
    input logic clkB,
    input logic FlagOut_clkB,
    input logic rst_n,
    // Internal DUT signals for binding
    input logic FlagToggle_clkA,
    input logic [2:0] SyncA_clkB
);
    ///// Reset behavior /////
    // FlagToggle_clkA must be 0 while reset is asserted.
    check_toggle_reset_value: assert property (
        @(posedge clkA) !rst_n |-> (FlagToggle_clkA == 1'b0)
    );
    // SyncA_clkB must be 0 while reset is asserted.
    check_sync_reset_value: assert property (
        @(posedge clkB) !rst_n |-> (SyncA_clkB == 3'b000)
    );
    // FlagOut_clkB must be 0 while reset is asserted.
    check_flagout_reset_low: assert property (
        @(posedge clkB) !rst_n |-> (FlagOut_clkB == 1'b0)
    );

    ///// clkA domain: toggle generation /////
    // FlagToggle_clkA updates as previous value XOR FlagIn_clkA.
    check_toggle_update_rule: assert property (
        @(posedge clkA) disable iff (!rst_n) $past(rst_n) |-> (FlagToggle_clkA == ($past(FlagToggle_clkA) ^ $past(FlagIn_clkA)))
    );
    // If FlagIn_clkA is 1, FlagToggle_clkA must change on this clkA edge.
    check_toggle_changes_on_one: assert property (
        @(posedge clkA) disable iff (!rst_n) $past(rst_n) && (FlagIn_clkA == 1'b1) |-> $changed(FlagToggle_clkA)
    );
    // If FlagIn_clkA is 0, FlagToggle_clkA must hold its value.
    check_toggle_stable_on_zero: assert property (
        @(posedge clkA) disable iff (!rst_n) $past(rst_n) && (FlagIn_clkA == 1'b0) |-> $stable(FlagToggle_clkA)
    );

    ///// clkB domain: 3FF synchronizer and edge detect /////
    // Upper two bits shift from lower two bits each clkB cycle.
    check_sync_shift_upper: assert property (
        @(posedge clkB) disable iff (!rst_n) $past(rst_n) |-> (SyncA_clkB[2:1] == $past(SyncA_clkB[1:0]))
    );
    // LSB captures FlagToggle_clkA sampled on the previous clkB edge.
    check_sync_captures_toggle: assert property (
        @(posedge clkB) disable iff (!rst_n) $past(rst_n) |-> (SyncA_clkB[0] == $past(FlagToggle_clkA))
    );
    // FlagOut_clkB equals XOR of SyncA_clkB[2] and SyncA_clkB[1].
    check_flagout_definition: assert property (
        @(posedge clkB) disable iff (!rst_n) (FlagOut_clkB == (SyncA_clkB[2] ^ SyncA_clkB[1]))
    );
    // FlagOut_clkB equals XOR of previous SyncA_clkB[1] and SyncA_clkB[0].
    check_flagout_prev_lower_equivalence: assert property (
        @(posedge clkB) disable iff (!rst_n) $past(rst_n) |-> (FlagOut_clkB == $past(SyncA_clkB[1] ^ SyncA_clkB[0]))
    );
endmodule