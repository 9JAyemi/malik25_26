module non_inverting_amp_sva (
    input logic clk,
    input logic reset,
    input logic [15:0] sine_out,
    input logic [15:0] amp_out
);
    // Expected constant output when not in reset (Vplus=16'h082A, Vplus*10=16'h51A4)
    localparam logic [15:0] AMP_CONST = 16'h51A4;

    ///// Reset behavior /////
    // During reset cycles, amp_out must be 0.
    amp_out_zero_during_reset: assert property (
        @(posedge clk) reset |-> (amp_out == 16'h0000)
    );

    // On reset assertion edge, amp_out updates to 0 in the same cycle.
    amp_out_zero_on_reset_rise: assert property (
        @(posedge clk) $rose(reset) |-> (amp_out == 16'h0000)
    );

    // On reset deassertion edge, amp_out updates to the constant in the same cycle.
    amp_out_const_on_reset_fall: assert property (
        @(posedge clk) $fell(reset) |-> (amp_out == AMP_CONST)
    );

    ///// Normal operation /////
    // When not in reset, amp_out must equal the constant value every cycle.
    amp_out_const_when_running: assert property (
        @(posedge clk) disable iff (reset) (amp_out == AMP_CONST)
    );

    // Once out of reset for at least one cycle, amp_out remains stable each cycle.
    amp_out_stable_while_running: assert property (
        @(posedge clk) disable iff (reset) $past(!reset) |-> (amp_out == $past(amp_out))
    );
endmodule