module add_sub_shift_sva (
    input logic [15:0] in0,
    input logic [15:0] in1,
    input logic ctrl,
    input logic signed [3:0] SHIFT,
    input logic RESET,
    input logic clk,
    input logic [15:0] q
);
    ///// Reset behavior /////
    // While RESET is high, q must be 0 on each clock.
    check_reset_forces_zero: assert property (
        @(posedge clk) RESET |-> (q == 16'h0000)
    );
    // On a rising edge of RESET, q must be 0 at that clock.
    check_reset_rise_clears_q: assert property (
        @(posedge clk) $rose(RESET) |-> (q == 16'h0000)
    );

    ///// Core functionality /////
    // When not in reset and ctrl=1, q equals (in0+in1) left-shifted by SHIFT at the same clock.
    check_add_path_q_correct: assert property (
        @(posedge clk) disable iff (RESET) (ctrl) |-> (q == ((in0 + in1) << SHIFT))
    );
    // When not in reset and ctrl=0, q equals (in0-in1) left-shifted by SHIFT at the same clock.
    check_sub_path_q_correct: assert property (
        @(posedge clk) disable iff (RESET) (!ctrl) |-> (q == ((in0 - in1) << SHIFT))
    );

    ///// Useful corollaries from the RTL math /////
    // If SHIFT==0, q equals add/sub result without shift.
    check_no_shift_when_SHIFT_zero: assert property (
        @(posedge clk) disable iff (RESET) (SHIFT == '0) |-> (q == (ctrl ? (in0 + in1) : (in0 - in1)))
    );
    // If ctrl=1 and in1==0, q equals in0 left-shifted by SHIFT.
    check_add_with_zero_rhs_equals_in0_shifted: assert property (
        @(posedge clk) disable iff (RESET) (ctrl && (in1 == 16'h0000)) |-> (q == (in0 << SHIFT))
    );
    // If ctrl=0 and in1==0, q equals in0 left-shifted by SHIFT.
    check_sub_with_zero_rhs_equals_in0_shifted: assert property (
        @(posedge clk) disable iff (RESET) (!ctrl && (in1 == 16'h0000)) |-> (q == (in0 << SHIFT))
    );
    // If ctrl=0 and in0==in1, q must be 0 (0 shifted remains 0).
    check_sub_equal_operands_zero: assert property (
        @(posedge clk) disable iff (RESET) (!ctrl && (in0 == in1)) |-> (q == 16'h0000)
    );

    ///// Stability /////
    // If inputs (in0,in1,ctrl,SHIFT) are stable across cycles and not in reset, q remains stable.
    check_stability_when_inputs_stable: assert property (
        @(posedge clk) disable iff (RESET)
            ($past(1'b1) && !$past(RESET) && $stable(in0) && $stable(in1) && $stable(ctrl) && $stable(SHIFT))
            |-> (q == $past(q))
    );
endmodule