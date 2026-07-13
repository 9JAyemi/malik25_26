module write_axi_sva (
    input logic clock_recovery,
    input logic clock_50,
    input logic reset_n,
    input logic [13:0] data_rec,
    input logic [13:0] data_stand
);
    // During active-low reset, data_stand is driven to zero.
    check_reset_drives_zero: assert property (
        @(posedge clock_50) !reset_n |-> (data_stand == 14'd0)
    );

    // When clock_recovery is HIGH, data_stand loads data_rec in the same cycle.
    check_update_when_cr_high: assert property (
        @(posedge clock_50) disable iff (!reset_n) clock_recovery |-> (data_stand == data_rec)
    );

    // When clock_recovery is LOW, data_stand holds its previous value.
    check_hold_when_cr_low: assert property (
        @(posedge clock_50) disable iff (!reset_n) !clock_recovery |-> (data_stand == $past(data_stand))
    );

    // Any change on data_stand must coincide with clock_recovery HIGH.
    check_change_requires_cr: assert property (
        @(posedge clock_50) disable iff (!reset_n) $changed(data_stand) |-> clock_recovery
    );

    // If a HIGH clock_recovery is followed by LOW, data_stand holds the sampled data_rec from the HIGH cycle.
    check_after_cr_high_then_low_holds_prev_sample: assert property (
        @(posedge clock_50) disable iff (!reset_n) $past(clock_recovery) && !clock_recovery |-> (data_stand == $past(data_rec))
    );

    // After reset release, data_stand stays zero until the first cycle with clock_recovery HIGH.
    check_zero_until_first_cr_after_reset_release: assert property (
        @(posedge clock_50) disable iff (!reset_n) $rose(reset_n) |-> (data_stand == 14'd0) until (clock_recovery)
    );

    // On clock_recovery HIGH, if data_rec differs from previous data_stand, data_stand must change.
    check_update_changes_when_new_diff_from_old: assert property (
        @(posedge clock_50) disable iff (!reset_n) clock_recovery && (data_rec != $past(data_stand)) |-> $changed(data_stand)
    );

    // On clock_recovery HIGH, if data_rec equals previous data_stand, data_stand must not change.
    check_update_no_change_when_new_equals_old: assert property (
        @(posedge clock_50) disable iff (!reset_n) clock_recovery && (data_rec == $past(data_stand)) |-> !$changed(data_stand)
    );
endmodule