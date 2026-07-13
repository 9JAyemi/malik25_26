module sysgen_logical_8b7810a2aa_sva (
    input logic [0:0] d0,
    input logic [0:0] d1,
    input logic [0:0] y,
    input logic clk,
    input logic ce,
    input logic clr
);
    // Output equals bitwise OR of inputs.
    check_or_function: assert property (
        @(posedge clk) disable iff (clr) (y == (d0 | d1))
    );

    // Output is 1 when either input is 1.
    check_output_high_when_any_high: assert property (
        @(posedge clk) disable iff (clr) ((d0 == 1'b1) || (d1 == 1'b1)) |-> (y == 1'b1)
    );

    // Output is 0 when both inputs are 0.
    check_output_low_when_both_low: assert property (
        @(posedge clk) disable iff (clr) ((d0 == 1'b0) && (d1 == 1'b0)) |-> (y == 1'b0)
    );

    // If output is 0, both inputs must be 0.
    check_zero_implies_both_zero: assert property (
        @(posedge clk) disable iff (clr) (y == 1'b0) |-> ((d0 == 1'b0) && (d1 == 1'b0))
    );

    // If output is 1, at least one input must be 1.
    check_one_implies_any_one: assert property (
        @(posedge clk) disable iff (clr) (y == 1'b1) |-> ((d0 == 1'b1) || (d1 == 1'b1))
    );

    // When d1 is 0, output equals d0.
    check_equals_d0_when_d1_zero: assert property (
        @(posedge clk) disable iff (clr) (d1 == 1'b0) |-> (y == d0)
    );

    // When d0 is 0, output equals d1.
    check_equals_d1_when_d0_zero: assert property (
        @(posedge clk) disable iff (clr) (d0 == 1'b0) |-> (y == d1)
    );

    // With stable inputs across a cycle, output remains stable.
    check_stable_output_when_inputs_stable: assert property (
        @(posedge clk) disable iff (clr) $stable(d0) && $stable(d1) |-> $stable(y)
    );

    // Output changes only if at least one input changes.
    check_output_change_requires_input_change: assert property (
        @(posedge clk) disable iff (clr) $changed(y) |-> ($changed(d0) || $changed(d1))
    );

    // If inputs are known (not X/Z), output is known (not X/Z).
    check_no_unknown_output_when_inputs_known: assert property (
        @(posedge clk) disable iff (clr) (!$isunknown(d0) && !$isunknown(d1)) |-> !$isunknown(y)
    );

    // Changing ce alone cannot change output when inputs are stable.
    check_ce_change_no_effect_with_inputs_stable: assert property (
        @(posedge clk) disable iff (clr) $changed(ce) && $stable(d0) && $stable(d1) |-> $stable(y)
    );
endmodule