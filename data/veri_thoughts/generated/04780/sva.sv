module top_module_sva(
    input logic clk,
    input logic a,
    input logic b,
    input logic c,
    input logic d,
    input logic out_final
);

    // Output matches the two XOR stages feeding the final AND.
    check_out_final_function: assert property (
        @(posedge clk) out_final == ((a ^ b) & (c ^ d))
    );

    // If the first XOR stage is low, the final output must be low.
    check_first_xor_blocks_output: assert property (
        @(posedge clk) !(a ^ b) |-> !out_final
    );

    // If the second XOR stage is low, the final output must be low.
    check_second_xor_blocks_output: assert property (
        @(posedge clk) !(c ^ d) |-> !out_final
    );

    // A high output requires both XOR stages to be high.
    check_output_high_requires_both_xors: assert property (
        @(posedge clk) out_final |-> ((a ^ b) && (c ^ d))
    );

    // If both XOR stages are high, the final output must be high.
    check_both_xors_drive_output_high: assert property (
        @(posedge clk) ((a ^ b) && (c ^ d)) |-> out_final
    );

endmodule