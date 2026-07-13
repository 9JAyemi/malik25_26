module pass_through_sva (
    input logic clk,
    input logic vdd18,
    input logic [7:0] in,
    input logic [7:0] out
);

    // Out equals in when vdd18=1, else zero.
    check_functional_mapping: assert property (
        @(posedge clk) out == (vdd18 ? in : 8'h00)
    );

    // On vdd18 rising edge, out equals in.
    check_on_power_rise: assert property (
        @(posedge clk) $rose(vdd18) |-> (out == in)
    );

    // On vdd18 falling edge, out is zero.
    check_on_power_fall: assert property (
        @(posedge clk) $fell(vdd18) |-> (out == 8'h00)
    );

    // If in and vdd18 do not change, out does not change.
    check_output_stable_when_inputs_stable: assert property (
        @(posedge clk) (!$changed(in) && !$changed(vdd18)) |-> !$changed(out)
    );

    // Out changes only if in or vdd18 changes.
    check_output_change_has_cause: assert property (
        @(posedge clk) $changed(out) |-> ($changed(in) || $changed(vdd18))
    );

    // When vdd18=0 and in changes, out remains zero.
    check_ignore_input_when_power_low: assert property (
        @(posedge clk) (!vdd18 && $changed(in)) |-> (out == 8'h00)
    );

    // When vdd18=1 and in changes, out equals in.
    check_follow_input_when_power_high: assert property (
        @(posedge clk) (vdd18 && $changed(in)) |-> (out == in)
    );

    // Non-zero out implies vdd18 is high.
    check_nonzero_out_implies_power_high: assert property (
        @(posedge clk) (out != 8'h00) |-> vdd18
    );

endmodule