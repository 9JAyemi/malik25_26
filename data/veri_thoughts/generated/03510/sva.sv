module xor_module_sva (
    input logic clk,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic [3:0] out_comb_logic
);

    // Combinational DUT with no native reset; clk is the formal sampling clock.

    // Output vector matches the XOR of the two inputs.
    check_output_matches_xor: assert property (
        @(posedge clk) out_comb_logic == (a ^ b)
    );

    // Bit 0 of the output is a[0] XOR b[0].
    check_bit0_matches_xor: assert property (
        @(posedge clk) out_comb_logic[0] == (a[0] ^ b[0])
    );

    // Bit 1 of the output is a[1] XOR b[1].
    check_bit1_matches_xor: assert property (
        @(posedge clk) out_comb_logic[1] == (a[1] ^ b[1])
    );

    // Bit 2 of the output is a[2] XOR b[2].
    check_bit2_matches_xor: assert property (
        @(posedge clk) out_comb_logic[2] == (a[2] ^ b[2])
    );

    // Bit 3 of the output is a[3] XOR b[3].
    check_bit3_matches_xor: assert property (
        @(posedge clk) out_comb_logic[3] == (a[3] ^ b[3])
    );

    // Equal inputs produce a zero output.
    check_equal_inputs_zero: assert property (
        @(posedge clk) (a == b) |-> (out_comb_logic == 4'b0000)
    );

    // Zero on b passes a through to the output.
    check_b_zero_passes_a: assert property (
        @(posedge clk) (b == 4'b0000) |-> (out_comb_logic == a)
    );

    // Zero on a passes b through to the output.
    check_a_zero_passes_b: assert property (
        @(posedge clk) (a == 4'b0000) |-> (out_comb_logic == b)
    );

endmodule