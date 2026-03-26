module and_or_gate_sva (
    input logic clk,
    input logic in1,
    input logic in2,
    input logic out
);

    // Output implements the OR of the two inputs.
    check_output_matches_or: assert property (
        @(posedge clk) out == (in1 | in2)
    );

    // Output is LOW when both inputs are LOW.
    check_output_low_when_both_inputs_low: assert property (
        @(posedge clk) ((in1 == 1'b0) && (in2 == 1'b0)) |-> (out == 1'b0)
    );

    // Output is HIGH whenever in1 is HIGH.
    check_output_high_when_in1_high: assert property (
        @(posedge clk) (in1 == 1'b1) |-> (out == 1'b1)
    );

    // Output is HIGH whenever in2 is HIGH.
    check_output_high_when_in2_high: assert property (
        @(posedge clk) (in2 == 1'b1) |-> (out == 1'b1)
    );

    // A HIGH output requires at least one HIGH input.
    check_output_high_requires_high_input: assert property (
        @(posedge clk) (out == 1'b1) |-> ((in1 == 1'b1) || (in2 == 1'b1))
    );

endmodule