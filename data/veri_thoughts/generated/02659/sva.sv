module and_gate_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic out
);
    // Output equals logical AND of inputs.
    check_and_equivalence: assert property (
        @(posedge clk) out == (a & b)
    );

    // Truth table: 0 & 0 -> 0.
    check_tt_00: assert property (
        @(posedge clk) (!a && !b) |-> (out == 1'b0)
    );

    // Truth table: 0 & 1 -> 0.
    check_tt_01: assert property (
        @(posedge clk) (!a && b) |-> (out == 1'b0)
    );

    // Truth table: 1 & 0 -> 0.
    check_tt_10: assert property (
        @(posedge clk) (a && !b) |-> (out == 1'b0)
    );

    // Truth table: 1 & 1 -> 1.
    check_tt_11: assert property (
        @(posedge clk) (a && b) |-> (out == 1'b1)
    );

    // Output rising requires both inputs HIGH.
    check_out_rise_requires_inputs_high: assert property (
        @(posedge clk) $rose(out) |-> (a && b)
    );

    // Output falling requires at least one input LOW.
    check_out_fall_requires_one_low: assert property (
        @(posedge clk) $fell(out) |-> (!a || !b)
    );

    // Output changes only when at least one input changes.
    check_out_change_requires_input_change: assert property (
        @(posedge clk) $changed(out) |-> ($changed(a) || $changed(b))
    );

    // Stable inputs imply stable output.
    check_stable_inputs_keep_output_stable: assert property (
        @(posedge clk) ($stable(a) && $stable(b)) |-> $stable(out)
    );

    // A rising with B HIGH sets output HIGH.
    check_a_rise_with_b_high_sets_out: assert property (
        @(posedge clk) ($rose(a) && b) |-> (out == 1'b1)
    );

    // B rising with A HIGH sets output HIGH.
    check_b_rise_with_a_high_sets_out: assert property (
        @(posedge clk) ($rose(b) && a) |-> (out == 1'b1)
    );

    // A falling with B HIGH clears output LOW.
    check_a_fall_with_b_high_clears_out: assert property (
        @(posedge clk) ($fell(a) && b) |-> (out == 1'b0)
    );

    // B falling with A HIGH clears output LOW.
    check_b_fall_with_a_high_clears_out: assert property (
        @(posedge clk) ($fell(b) && a) |-> (out == 1'b0)
    );
endmodule