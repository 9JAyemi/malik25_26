module top_module_sva (
    input logic clk,
    input logic [3:0] multiplier,
    input logic [3:0] multiplicand,
    input logic [15:0] in0,
    input logic [15:0] in1,
    input logic ctrl,
    input logic [15:0] out
);
    // Note: DUT is purely combinational with no reset; assertions are sampled on clk with no disable.

    // Helper expressions matching DUT math
    let prod8_l  = (multiplier * multiplicand);                  // 8-bit product
    let sum4_l   = (multiplier + multiplicand);                  // 4-bit add (wrap)
    let diff4_l  = (multiplier - multiplicand);                  // 4-bit sub (wrap)
    let final0_l = {8'b0, prod8_l} + {12'b0, sum4_l};            // functional_module(out) when ctrl==0
    let final1_l = {8'b0, prod8_l} + {12'b0, diff4_l};           // functional_module(out) when ctrl==1

    // When ctrl==0, out equals functional_module result (product + add) zero-extended.
    check_ctrl0_out_equation: assert property (
        @(posedge clk) disable iff (1'b0)
            (ctrl == 1'b0) |-> (out == final0_l)
    );

    // When ctrl==1, out equals functional result (product + sub) plus in0 and in1 (16-bit wrap).
    check_ctrl1_out_equation: assert property (
        @(posedge clk) disable iff (1'b0)
            (ctrl == 1'b1) |-> (out == (final1_l + in0 + in1))
    );

    // Under ctrl==0, upper 8 bits of out are zero (result fits in 8 bits after nibble add).
    check_ctrl0_upper_zero: assert property (
        @(posedge clk) disable iff (1'b0)
            (ctrl == 1'b0) |-> (out[15:8] == 8'h00)
    );

    // If all inputs are stable, out remains stable (purely combinational function).
    check_stable_when_inputs_stable: assert property (
        @(posedge clk) disable iff (1'b0)
            $stable({multiplier, multiplicand, ctrl, in0, in1}) |-> $stable(out)
    );

    // Under ctrl==0, with ctrl/multiplier/multiplicand stable, out is stable (ignores in0/in1).
    check_ctrl0_independent_of_in0_in1: assert property (
        @(posedge clk) disable iff (1'b0)
            (ctrl == 1'b0 && $stable(ctrl) && $stable(multiplier) && $stable(multiplicand)) |-> $stable(out)
    );

    // Under ctrl==0, low nibble equals (prod[3:0] + (a+b))[3:0].
    check_ctrl0_low_nibble: assert property (
        @(posedge clk) disable iff (1'b0)
            (ctrl == 1'b0) |-> (out[3:0] == ((prod8_l[3:0] + sum4_l)[3:0]))
    );

    // Under ctrl==0, out is within the computed bound (<= 240).
    check_ctrl0_range_bound: assert property (
        @(posedge clk) disable iff (1'b0)
            (ctrl == 1'b0) |-> (out <= 16'd240)
    );

    // Under ctrl==1 and in0==0 and in1==0, out reduces to functional result (product + sub).
    check_ctrl1_zero_ext_inputs: assert property (
        @(posedge clk) disable iff (1'b0)
            (ctrl == 1'b1 && in0 == 16'h0000 && in1 == 16'h0000) |-> (out == final1_l)
    );

    // On ctrl falling edge, output selects the ctrl==0 path immediately.
    check_ctrl_fall_selects_ctrl0_path: assert property (
        @(posedge clk) disable iff (1'b0)
            $fell(ctrl) |-> (out == final0_l)
    );

    // On ctrl rising edge, output selects the ctrl==1 path immediately.
    check_ctrl_rise_selects_ctrl1_path: assert property (
        @(posedge clk) disable iff (1'b0)
            $rose(ctrl) |-> (out == (final1_l + in0 + in1))
    );

endmodule