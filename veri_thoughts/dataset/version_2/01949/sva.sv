module velocityControlHdl_Reset_Delay_sva (
    input logic CLK_IN,
    input logic reset,              // synchronous, active-HIGH
    input logic enb_1_2000_0,       // clock enable
    input logic Reset_1,            // active-HIGH zero gating
    input logic signed [31:0] In,
    input logic signed [31:0] Out
);
    // Analysis: CLK=CLK_IN; sync reset=reset (active-HIGH). Mixed logic: reg In_Delay_out1 with enable; combinational gating by Reset_1. Out=0 when Reset_1=1; else Out follows registered path; reset loads reg to 0.

    // Out must be zero whenever Reset_1 is HIGH.
    check_out_zero_when_reset1_high: assert property (
        @(posedge CLK_IN) disable iff (reset) (Reset_1 == 1'b1) |-> (Out == 32'sd0)
    );

    // If Reset_1 is HIGH in two consecutive cycles, Out stays 0 and stable.
    check_out_stable_while_reset1_high: assert property (
        @(posedge CLK_IN) disable iff (reset) ($past(Reset_1) == 1'b1 && Reset_1 == 1'b1) |-> (Out == 32'sd0 && Out == $past(Out))
    );

    // One cycle after synchronous reset is asserted, Out must be zero.
    check_out_zero_one_cycle_after_reset: assert property (
        @(posedge CLK_IN) $past(reset) == 1'b1 |-> (Out == 32'sd0)
    );

    // With Reset_1 LOW in consecutive cycles and enable LOW, Out holds its value.
    check_hold_out_when_no_en_and_reset1_low: assert property (
        @(posedge CLK_IN) disable iff (reset) (Reset_1 == 1'b0 && $past(Reset_1) == 1'b0 && enb_1_2000_0 == 1'b0 && $past(reset) == 1'b0) |-> (Out == $past(Out))
    );

    // If enable was HIGH and Reset_1 LOW in the previous cycle (no reset), previous Out equaled previous In.
    check_prev_out_eq_prev_in_when_prev_en_and_reset1_low: assert property (
        @(posedge CLK_IN) disable iff (reset) ($past(enb_1_2000_0) == 1'b1 && $past(Reset_1) == 1'b0 && $past(reset) == 1'b0) |-> ($past(Out) == $past(In))
    );

    // If enable was LOW and Reset_1 LOW for two cycles (no reset), previous Out held its value.
    check_prev_hold_two_cycle_when_no_en: assert property (
        @(posedge CLK_IN) disable iff (reset) ($past(enb_1_2000_0) == 1'b0 && $past(Reset_1) == 1'b0 && $past(reset) == 1'b0 && $past(Reset_1,2) == 1'b0) |-> ($past(Out) == $past(Out,2))
    );

    // Capture then hold: en=1 with Reset_1=0, then en=0 next cycle with Reset_1=0 => Out equals captured In.
    check_capture_then_hold_propagates_input: assert property (
        @(posedge CLK_IN) disable iff (reset)
            ((Reset_1 == 1'b0) && (enb_1_2000_0 == 1'b1) && (reset == 1'b0)) ##1
            ((Reset_1 == 1'b0) && (enb_1_2000_0 == 1'b0) && (reset == 1'b0))
            |-> (Out == $past(In,1))
    );

    // If zero was captured (Reset_1=1 with en=1), then next cycle with Reset_1=0 and en=0, Out remains 0.
    check_zero_load_then_hold_results_zero: assert property (
        @(posedge CLK_IN) disable iff (reset)
            ((Reset_1 == 1'b1) && (enb_1_2000_0 == 1'b1) && (reset == 1'b0)) ##1
            ((Reset_1 == 1'b0) && (enb_1_2000_0 == 1'b0) && (reset == 1'b0))
            |-> (Out == 32'sd0)
    );

    // On rising edge of Reset_1, Out is immediately driven to 0.
    check_out_zero_on_reset1_rise: assert property (
        @(posedge CLK_IN) disable iff (reset) $rose(Reset_1) |-> (Out == 32'sd0)
    );

endmodule