module velocityControlHdl_Reset_Delay_sva (
    input logic        CLK_IN,
    input logic        reset,
    input logic        enb_1_2000_0,
    input logic        Reset_1,
    input logic signed [31:0] In,
    input logic signed [31:0] Out
);

// Reset high forces Out to zero on the next cycle.
    check_reset_clears_out: assert property (
        @(posedge CLK_IN) reset |=> (Out == 32'sd0)
    );

// With enb_1_2000_0 low, Out holds its previous value.
    check_hold_when_disabled: assert property (
        @(posedge CLK_IN) disable iff (reset)
        (!enb_1_2000_0) |=> (Out == $past(Out))
    );

// With enb_1_2000_0 high and Reset_1 low, Out captures In.
    check_capture_in_when_enabled: assert property (
        @(posedge CLK_IN) disable iff (reset)
        (enb_1_2000_0 && !Reset_1) |=> (Out == $past(In))
    );

// With enb_1_2000_0 high and Reset_1 high, Out captures zero.
    check_capture_zero_when_enabled: assert property (
        @(posedge CLK_IN) disable iff (reset)
        (enb_1_2000_0 && Reset_1) |=> (Out == 32'sd0)
    );

endmodule
