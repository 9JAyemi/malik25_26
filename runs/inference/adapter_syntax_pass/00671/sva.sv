module xor_gate_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic out_comb
);

    // out_comb must match the RTL XOR expression.
    check_out_matches_rtl_expression: assert property (
        @(posedge clk) out_comb == ((a & ~b) | (~a & b))
    );

    // out_comb must equal the XOR of a and b.
    check_out_matches_xor_function: assert property (
        @(posedge clk) out_comb == (a ^ b)
    );

    // When a and b are equal, out_comb must be low.
    check_equal_inputs_drive_low: assert property (
        @(posedge clk) (a == b) |-> (out_comb == 1'b0)
    );

    // When a and b differ, out_comb must be high.
    check_different_inputs_drive_high: assert property (
        @(posedge clk) (a != b) |-> (out_comb == 1'b1)
    );

endmodule