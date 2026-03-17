module v2be0f8_sva (
    input logic clk,
    input logic vd53b77,
    input logic v27dec4,
    input logic vf354ee,
    input logic v4642b6
);

    // Top output is always the OR of the two functional inputs.
    check_output_is_or_of_inputs: assert property (
        @(posedge clk) v4642b6 == (vd53b77 | v27dec4)
    );

    // Output is low when both OR inputs are low.
    check_output_low_on_00: assert property (
        @(posedge clk) (!vd53b77 && !v27dec4) |-> !v4642b6
    );

    // A high vd53b77 forces the output high.
    check_output_high_when_vd53b77_high: assert property (
        @(posedge clk) vd53b77 |-> v4642b6
    );

    // A high v27dec4 forces the output high.
    check_output_high_when_v27dec4_high: assert property (
        @(posedge clk) v27dec4 |-> v4642b6
    );

    // The vf354ee input does not affect the top-level output.
    check_vf354ee_does_not_influence_output: assert property (
        @(posedge clk) ($changed(vf354ee) && $stable(vd53b77) && $stable(v27dec4)) |-> $stable(v4642b6)
    );

    // Holding the OR inputs steady keeps the output steady.
    check_output_stable_when_or_inputs_stable: assert property (
        @(posedge clk) ($stable(vd53b77) && $stable(v27dec4)) |-> $stable(v4642b6)
    );

endmodule