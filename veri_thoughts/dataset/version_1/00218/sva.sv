module signed_multiplier_32_sva #(
    parameter ID = 32'd1,
    parameter NUM_STAGE = 32'd1,
    parameter din0_WIDTH = 32'd1,
    parameter din1_WIDTH = 32'd1,
    parameter dout_WIDTH = 32'd1
) (
    input logic clk,
    input logic reset,
    input logic ce,
    input logic signed [din0_WIDTH - 1:0] din0,
    input logic signed [din1_WIDTH - 1:0] din1,
    input logic signed [dout_WIDTH + din0_WIDTH - 1:0] dout
);

    // Reset clears the registered output value.
    check_reset_clears_output: assert property (
        @(posedge clk) reset |=> (dout == '0)
    );

    // With clock enable low, the output holds its prior value.
    check_hold_when_ce_low: assert property (
        @(posedge clk) disable iff (reset)
        (!ce) |=> (dout == $past(dout))
    );

    // An enabled update drives the output to zero.
    check_enable_update_clears_output: assert property (
        @(posedge clk) disable iff (reset)
        ce |=> (dout == '0)
    );

    // The widened output is always a sign-extension of the stored value.
    check_output_sign_extension: assert property (
        @(posedge clk) disable iff (reset)
        dout[dout_WIDTH + din0_WIDTH - 1:dout_WIDTH] == {din0_WIDTH{dout[dout_WIDTH - 1]}}
    );

    // Input changes do not bypass the register when clock enable is low.
    check_input_changes_ignored_when_ce_low: assert property (
        @(posedge clk) disable iff (reset)
        (!ce && ($changed(din0) || $changed(din1))) |=> (dout == $past(dout))
    );

    // A zero output is retained across idle cycles.
    check_zero_retained_when_idle: assert property (
        @(posedge clk) disable iff (reset)
        (!ce && (dout == '0)) |=> (dout == '0)
    );

endmodule