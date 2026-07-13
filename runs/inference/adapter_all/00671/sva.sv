module xor_gate_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic out_comb
);

    // Output must match the implemented XOR function.
    check_out_matches_xor_function: assert property (
        @(posedge clk) out_comb == ((a & ~b) | (~a & b))
    );

    // When both inputs are low, the output must be low.
    check_both_low_drive_low: assert property (
        @(posedge clk) (!a && !b) |-> (out_comb == 1'b0)
    );

    // When only a is high, the output must be high.
    check_only_a_high_drive_high: assert property (
        @(posedge clk) (a && !b) |-> (out_comb == 1'b1)
    );

    // When only b is high, the output must be high.
    check_only_b_high_drive_high: assert property (
        @(posedge clk) (!a && b) |-> (out_comb == 1'b1)
    );

    // When both inputs are high, the output must be low.
    check_both_high_drive_low: assert property (
        @(posedge clk) (a && b) |-> (out_comb == 1'b0)
    );

    // A high output must come from exactly one asserted input.
    check_high_output_requires_one_hot: assert property (
        @(posedge clk) out_comb |-> ((a && !b) || (!a && b))
    );

    // A low output must come from both inputs being equal.
    check_low_output_requires_equal_inputs: assert property (
        @(posedge clk) !out_comb |-> ((a && b) || (!a && !b))
    );

endmodule