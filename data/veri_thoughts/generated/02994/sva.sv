module and_gate_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic out
);
    // Output equals bitwise AND of inputs at every sample.
    check_out_equals_and: assert property (
        @(posedge clk) out == (a & b)
    );

    // Output high implies both inputs are high.
    check_out_high_implies_inputs_high: assert property (
        @(posedge clk) out |-> (a & b)
    );

    // If input a is 0, output must be 0.
    check_zero_a_forces_zero_out: assert property (
        @(posedge clk) !a |-> !out
    );

    // If input b is 0, output must be 0.
    check_zero_b_forces_zero_out: assert property (
        @(posedge clk) !b |-> !out
    );

    // If input a is 1, output equals b.
    check_a_one_equals_b: assert property (
        @(posedge clk) a |-> (out == b)
    );

    // If input b is 1, output equals a.
    check_b_one_equals_a: assert property (
        @(posedge clk) b |-> (out == a)
    );

    // If both inputs are 1, output must be 1.
    check_both_one_outputs_one: assert property (
        @(posedge clk) (a & b) |-> out
    );

    // If inputs are stable across samples, output is stable too.
    check_stability_when_inputs_stable: assert property (
        @(posedge clk) ((a == $past(a)) && (b == $past(b))) |-> (out == $past(out))
    );

    // Output can only change if at least one input changes.
    check_out_changes_only_on_input_change: assert property (
        @(posedge clk) (out != $past(out)) |-> ((a != $past(a)) || (b != $past(b)))
    );
endmodule