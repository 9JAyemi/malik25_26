module omsp_wakeup_cell_sva (
    input  logic scan_clk,     // Scan clock
    input  logic scan_mode,    // Scan mode
    input  logic scan_rst,     // Scan reset (active high)
    input  logic wkup_clear,   // Functional reset (active high)
    input  logic wkup_event,   // Functional event clock
    input  logic wkup_out      // Wakeup output
);

    ///// Functional mode (scan_mode == 0) /////
    // In functional mode, a rising wkup_clear drives wkup_out low.
    check_func_clear_drives_zero: assert property (
        @(posedge wkup_clear) (scan_mode == 1'b0) |=> ##0 (wkup_out == 1'b0)
    );

    // In functional mode, a rising wkup_event with clear deasserted sets wkup_out high.
    check_func_event_sets_one: assert property (
        @(posedge wkup_event) disable iff (wkup_clear)
            (scan_mode == 1'b0) |=> ##0 (wkup_out == 1'b1)
    );

    // In functional mode, a rising wkup_event keeps wkup_out high if already high and not clearing.
    check_func_event_keeps_one: assert property (
        @(posedge wkup_event) disable iff (wkup_clear)
            (scan_mode == 1'b0 && wkup_out == 1'b1) |=> ##0 (wkup_out == 1'b1)
    );

    // In functional mode, if wkup_out was low, a rising wkup_event with clear deasserted sets it high.
    check_func_event_sets_one_when_prev_zero: assert property (
        @(posedge wkup_event) disable iff (wkup_clear)
            (scan_mode == 1'b0 && $past(wkup_out) == 1'b0) |=> ##0 (wkup_out == 1'b1)
    );

    // In functional mode, clear dominates if wkup_event and clear coincide.
    check_func_event_with_clear_dominates: assert property (
        @(posedge wkup_event) (scan_mode == 1'b0 && wkup_clear == 1'b1) |=> ##0 (wkup_out == 1'b0)
    );

    ///// Scan mode (scan_mode == 1) /////
    // In scan mode, a rising scan_rst drives wkup_out low.
    check_scan_rst_drives_zero: assert property (
        @(posedge scan_rst) (scan_mode == 1'b1) |=> ##0 (wkup_out == 1'b0)
    );

    // In scan mode, a rising scan_clk with scan_rst deasserted sets wkup_out high.
    check_scan_clk_sets_one: assert property (
        @(posedge scan_clk) disable iff (scan_rst)
            (scan_mode == 1'b1) |=> ##0 (wkup_out == 1'b1)
    );

    // In scan mode, a rising scan_clk keeps wkup_out high if already high and not resetting.
    check_scan_clk_keeps_one: assert property (
        @(posedge scan_clk) disable iff (scan_rst)
            (scan_mode == 1'b1 && wkup_out == 1'b1) |=> ##0 (wkup_out == 1'b1)
    );

    // In scan mode, if wkup_out was low, a rising scan_clk with scan_rst deasserted sets it high.
    check_scan_clk_sets_one_when_prev_zero: assert property (
        @(posedge scan_clk) disable iff (scan_rst)
            (scan_mode == 1'b1 && $past(wkup_out) == 1'b0) |=> ##0 (wkup_out == 1'b1)
    );

    // In scan mode, reset dominates if scan_clk and scan_rst coincide.
    check_scan_clk_with_rst_dominates: assert property (
        @(posedge scan_clk) (scan_mode == 1'b1 && scan_rst == 1'b1) |=> ##0 (wkup_out == 1'b0)
    );

endmodule