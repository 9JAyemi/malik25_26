module AND_32bit_sva (
    input logic        clk,
    input logic [31:0] out,
    input logic [31:0] A,
    input logic [31:0] B
);

    // RTL has no clock or reset; clk is an external sampling clock.

    // Output equals the bitwise AND of the two inputs.
    check_out_matches_bitwise_and: assert property (
        @(posedge clk) out == (A & B)
    );

    // A value of zero forces the output to zero.
    check_zero_a_forces_zero_out: assert property (
        @(posedge clk) (A == 32'h0000_0000) |-> (out == 32'h0000_0000)
    );

    // B value of zero forces the output to zero.
    check_zero_b_forces_zero_out: assert property (
        @(posedge clk) (B == 32'h0000_0000) |-> (out == 32'h0000_0000)
    );

    // All ones on A makes the output follow B.
    check_all_ones_a_passes_b: assert property (
        @(posedge clk) (A == 32'hFFFF_FFFF) |-> (out == B)
    );

    // All ones on B makes the output follow A.
    check_all_ones_b_passes_a: assert property (
        @(posedge clk) (B == 32'hFFFF_FFFF) |-> (out == A)
    );

    // Any high output bit must also be high in A.
    check_output_ones_subset_of_a: assert property (
        @(posedge clk) ((out & ~A) == 32'h0000_0000)
    );

    // Any high output bit must also be high in B.
    check_output_ones_subset_of_b: assert property (
        @(posedge clk) ((out & ~B) == 32'h0000_0000)
    );

    // Equal inputs pass through unchanged to the output.
    check_equal_inputs_pass_through: assert property (
        @(posedge clk) (A == B) |-> (out == A)
    );

endmodule