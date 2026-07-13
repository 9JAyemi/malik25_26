module ClockGating_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic RESET,
    input logic ENCLK
);

    // Any reset cycle leaves ENCLK low by the next observed clock.
    check_reset_clears_enclk: assert property (
        @(posedge CLK) RESET |=> (ENCLK == 1'b0)
    );

    // With EN low, the RTL takes the else branch and drives ENCLK low.
    check_en_low_drives_enclk_low: assert property (
        @(posedge CLK) disable iff (RESET) (!EN) |=> (ENCLK == 1'b0)
    );

    // With EN and TE high, the TE branch drives ENCLK low.
    check_te_high_drives_enclk_low: assert property (
        @(posedge CLK) disable iff (RESET) (EN && TE) |=> (ENCLK == 1'b0)
    );

    // With EN high and TE low, ~CLK at posedge CLK evaluates to 0.
    check_enabled_branch_drives_enclk_low: assert property (
        @(posedge CLK) disable iff (RESET) (EN && !TE) |=> (ENCLK == 1'b0)
    );

    // Every non-reset clocked update results in ENCLK being low.
    check_all_active_clock_updates_drive_low: assert property (
        @(posedge CLK) disable iff (RESET) 1'b1 |=> (ENCLK == 1'b0)
    );

endmodule