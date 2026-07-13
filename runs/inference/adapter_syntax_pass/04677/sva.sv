module xor_gate_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic y
);

    // y matches the implemented NAND-based XOR function.
    check_output_matches_implemented_function: assert property (
        @(posedge clk) y == ~((~a & ~b) | (a & b))
    );

    // y is low when both inputs are low.
    check_output_low_when_both_inputs_low: assert property (
        @(posedge clk) (!a && !b) |-> !y
    );

    // y is high when exactly one input is high.
    check_output_high_when_one_input_high: assert property (
        @(posedge clk) ((a && !b) || (!a && b)) |-> y
    );

    // y is low when both inputs are high.
    check_output_low_when_both_inputs_high: assert property (
        @(posedge clk) (a && b) |-> !y
    );

endmodule