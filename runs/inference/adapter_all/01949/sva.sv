module velocityControlHdl_Reset_Delay_sva (
    input logic        CLK_IN,
    input logic        reset,
    input logic        enb_1_2000_0,
    input logic        Reset_1,
    input logic signed [31:0] In,
    input logic signed [31:0] Out
);

    // Reset clears the delayed output on the next clock.
    check_reset_clears_out: assert property (
        @(posedge CLK_IN) reset |=> (Out == 32'sd0)
    );

    // When enabled, the output captures In on the next clock.
    check_capture_on_enable: assert property (
        @(posedge CLK_IN) disable iff (reset)
        enb_1_2000_0 |=> (Out == $past(In))
    );

    // When not enabled, the output holds its previous value.
    check_hold_when_disabled: assert property (
        @(posedge CLK_IN) disable iff (reset)
        !enb_1_2000_0 |=> (Out == $past(Out))
    );

    // Reset has priority over enable when both are asserted.
    check_reset_priority_over_enable: assert property (
        @(posedge CLK_IN) (reset && enb_1_2000_0) |=> (Out == 32'sd0)
    );

    // Reset overrides the bypass path when Reset_1 is low.
    check_reset_bypass_override: assert property (
        @(posedge CLK_IN) (reset && !Reset_1) |=> (Out == 32'sd0)
    );

    // With enable and Reset_1 low, the output captures In.
    check_capture_on_enable_with_reset1_low: assert property (
        @(posedge CLK_IN) disable iff (reset)
        (enb_1_2000_0 && !Reset_1) |=> (Out == $past(In))
    );

    // With enable and Reset_1 high, the output captures the delayed In value.
    check_capture_on_enable_with_reset1_high: assert property (
        @(posedge CLK_IN) disable iff (reset)
        (enb_1_2000_0 && Reset_1) |=> (Out == $past(In, 2))
    );

endmodule