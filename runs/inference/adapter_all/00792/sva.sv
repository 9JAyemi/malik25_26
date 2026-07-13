module xor_module_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic out_comb_logic
);

    // Output must always equal the XOR of the inputs.
    check_xor_function: assert property (
        @(posedge clk) out_comb_logic == (a ^ b)
    );

    // When both inputs are low, the output must be low.
    check_both_low: assert property (
        @(posedge clk) (!a && !b) |-> !out_comb_logic
    );

    // When both inputs are high, the output must be low.
    check_both_high: assert property (
        @(posedge clk) (a && b) |-> !out_comb_logic
    );

    // When the inputs differ, the output must be high.
    check_inputs_differ: assert property (
        @(posedge clk) (a ^ b) |-> out_comb_logic
    );

    // A high output requires the inputs to differ.
    check_output_high_requires_xor: assert property (
        @(posedge clk) out_comb_logic |-> (a ^ b)
    );

endmodule