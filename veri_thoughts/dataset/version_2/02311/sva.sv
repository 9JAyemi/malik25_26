module and_gate_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic out
);
    // Output equals logical AND of inputs.
    check_out_is_and: assert property (
        @(posedge clk) out == (a & b)
    );

    // Output HIGH only if both inputs HIGH.
    check_out_high_requires_inputs_high: assert property (
        @(posedge clk) (out == 1'b1) |-> (a && b)
    );

    // If input a is LOW then output must be LOW.
    check_out_low_when_a_low: assert property (
        @(posedge clk) (!a) |-> (out == 1'b0)
    );

    // If input b is LOW then output must be LOW.
    check_out_low_when_b_low: assert property (
        @(posedge clk) (!b) |-> (out == 1'b0)
    );

    // If both inputs are HIGH then output must be HIGH.
    check_out_high_when_both_high: assert property (
        @(posedge clk) (a && b) |-> (out == 1'b1)
    );

    // A rising output implies both inputs are HIGH.
    check_out_rise_requires_inputs_high: assert property (
        @(posedge clk) $rose(out) |-> (a && b)
    );

    // A falling output implies at least one input is LOW.
    check_out_fall_requires_one_low: assert property (
        @(posedge clk) $fell(out) |-> (!a || !b)
    );
endmodule