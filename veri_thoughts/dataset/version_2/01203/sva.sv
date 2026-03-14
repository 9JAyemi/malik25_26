module clock_divider_sva (
    input logic iCLK,
    input logic iRST_n,
    input logic oCLK_OUT
);

    ///// Reset behavior /////
    // While reset is asserted, oCLK_OUT must be 0.
    reset_holds_output_low: assert property (
        @(posedge iCLK) (!iRST_n) |-> (oCLK_OUT == 1'b0)
    );

    // On the cycle reset is asserted (falling edge), oCLK_OUT must be 0.
    reset_fall_clears_output: assert property (
        @(posedge iCLK) $fell(iRST_n) |-> (oCLK_OUT == 1'b0)
    );

    // On the first active clock after reset deasserts, oCLK_OUT remains 0.
    post_reset_first_cycle_low: assert property (
        @(posedge iCLK) disable iff (!iRST_n) $rose(iRST_n) |-> (oCLK_OUT == 1'b0)
    );

    ///// Output well-formedness /////
    // Out of reset, oCLK_OUT must never be X/Z.
    check_output_known_when_active: assert property (
        @(posedge iCLK) disable iff (!iRST_n) !$isunknown(oCLK_OUT)
    );

    // Any change of oCLK_OUT can only occur when not in reset now and in the previous cycle.
    change_only_out_of_reset: assert property (
        @(posedge iCLK) $changed(oCLK_OUT) |-> (iRST_n && $past(iRST_n))
    );

    ///// Toggle pacing /////
    // oCLK_OUT cannot toggle on two consecutive cycles.
    no_back_to_back_toggles: assert property (
        @(posedge iCLK) disable iff (!iRST_n) $changed(oCLK_OUT) |-> ##1 !$changed(oCLK_OUT)
    );

    // After a rising edge, oCLK_OUT stays HIGH for at least one full cycle.
    min_high_pulse_width_1cycle: assert property (
        @(posedge iCLK) disable iff (!iRST_n) $rose(oCLK_OUT) |-> ##1 (oCLK_OUT == 1'b1)
    );

    // After a falling edge, oCLK_OUT stays LOW for at least one full cycle.
    min_low_pulse_width_1cycle: assert property (
        @(posedge iCLK) disable iff (!iRST_n) $fell(oCLK_OUT) |-> ##1 (oCLK_OUT == 1'b0)
    );

endmodule