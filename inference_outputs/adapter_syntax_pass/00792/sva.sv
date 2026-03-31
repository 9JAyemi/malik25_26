module xor_module_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic out_comb_logic
);

    // out_comb_logic must equal the XOR of a and b.
    check_xor_function: assert property (
        @(posedge clk) out_comb_logic == (a ^ b)
    );

    // When a and b are equal, out_comb_logic must be low.
    check_equal_inputs_drive_low: assert property (
        @(posedge clk) (a == b) |-> (out_comb_logic == 1'b0)
    );

    // When a and b differ, out_comb_logic must be high.
    check_different_inputs_drive_high: assert property (
        @(posedge clk) (a != b) |-> (out_comb_logic == 1'b1)
    );

endmodule