module velocityControlHdl_Reset_Delay_sva (
    input logic CLK_IN,
    input logic reset,
    input logic enb_1_2000_0,
    input logic Reset_1,
    input logic signed [31:0] In,
    input logic signed [31:0] Out
);

    // Reset clears the delayed output on the next clock.
    check_reset_clears_out: assert property (
        @(posedge CLK_IN) reset |=> (Out == 32'sd0)
    );

    // With enable low, the output holds its previous value.
    check_hold_when_disabled: assert property (
        @(posedge CLK_IN) disable iff (reset)
        (!enb_1_2000_0) |=> (Out == $past(Out))
    );

    // With enable high and Reset_1 low, the output captures In.
    check_capture_in_when_reset_low: assert property (
        @(posedge CLK_IN) disable iff (reset)
        (enb_1_2000_0 && (Reset_1 == 1'b0)) |=> (Out == $past(In))
    );

    // With enable high and Reset_1 high, the output clears to zero.
    check_clear_when_reset_high: assert property (
        @(posedge CLK_IN) disable iff (reset)
        (enb_1_2000_0 && (Reset_1 == 1'b1)) |=> (Out == 32'sd0)
    );

endmodule