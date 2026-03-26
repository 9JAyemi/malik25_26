module ResetToBool_sva (
    input logic RST,
    input logic VAL
);

    // VAL must equal the RTL reset comparison result.
    check_val_matches_reset_expr: assert property (
        @($global_clock) disable iff (1'b0)
        (VAL === (RST == 1'b0))
    );

    // A low RST input must drive VAL high.
    check_low_rst_drives_val_high: assert property (
        @($global_clock) disable iff (1'b0)
        (RST === 1'b0) |-> (VAL === 1'b1)
    );

    // A high RST input must drive VAL low.
    check_high_rst_drives_val_low: assert property (
        @($global_clock) disable iff (1'b0)
        (RST === 1'b1) |-> (VAL === 1'b0)
    );

    // An unknown RST input must produce an unknown VAL.
    check_unknown_rst_propagates_unknown_val: assert property (
        @($global_clock) disable iff (1'b0)
        $isunknown(RST) |-> $isunknown(VAL)
    );

endmodule