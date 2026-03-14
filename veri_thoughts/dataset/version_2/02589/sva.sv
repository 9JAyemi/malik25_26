module arithmetic_operations_sva (
    // DUT ports as inputs
    input logic [15:0] A_in,
    input logic [15:0] B_in,
    input logic [15:0] sum_out,
    input logic [15:0] diff_out,
    input logic [15:0] abs_diff_out,
    input logic [15:0] and_out,
    input logic [15:0] or_out,
    input logic [15:0] xor_out,
    // External sampling clock for SVA (RTL is combinational; no reset present)
    input logic CLK
);
    // Combinational RTL (no clock/reset). Assertions sample on CLK.
    // Behaviors: sum=A+B (16-bit wrap), diff=A-B (16-bit wrap), abs_diff per unsigned compare, bitwise AND/OR/XOR.

    // Sum equals lower 16 bits of A_in + B_in.
    check_sum_functional: assert property (
        @(posedge CLK) sum_out == (A_in + B_in)[15:0]
    );

    // Difference equals lower 16 bits of A_in - B_in.
    check_diff_functional: assert property (
        @(posedge CLK) diff_out == (A_in - B_in)[15:0]
    );

    // Absolute difference when A_in > B_in equals A_in - B_in.
    check_absdiff_when_gt: assert property (
        @(posedge CLK) (A_in > B_in) |-> (abs_diff_out == (A_in - B_in)[15:0])
    );

    // Absolute difference when A_in <= B_in equals B_in - A_in.
    check_absdiff_when_le: assert property (
        @(posedge CLK) (A_in <= B_in) |-> (abs_diff_out == (B_in - A_in)[15:0])
    );

    // Bitwise AND correctness.
    check_and_functional: assert property (
        @(posedge CLK) and_out == (A_in & B_in)
    );

    // Bitwise OR correctness.
    check_or_functional: assert property (
        @(posedge CLK) or_out == (A_in | B_in)
    );

    // Bitwise XOR correctness.
    check_xor_functional: assert property (
        @(posedge CLK) xor_out == (A_in ^ B_in)
    );

    // XOR equals (OR & ~AND).
    check_xor_or_and_identity: assert property (
        @(posedge CLK) xor_out == (or_out & ~and_out)
    );

    // OR equals XOR | AND.
    check_or_decomposition: assert property (
        @(posedge CLK) or_out == (xor_out | and_out)
    );

    // AND is a subset of OR (no bit can be 1 in AND while 0 in OR).
    check_and_subset_or: assert property (
        @(posedge CLK) (and_out & ~or_out) == 16'h0000
    );

    // When inputs are equal, diff/xor/abs_diff are zero.
    check_equal_inputs_zeroes: assert property (
        @(posedge CLK) (A_in == B_in) |-> (diff_out == 16'h0000) && (abs_diff_out == 16'h0000) && (xor_out == 16'h0000)
    );

endmodule