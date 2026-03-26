module top_module_sva (
    input logic        clk,
    input logic [99:0] in,
    input logic [3:0]  and_out,
    input logic [3:0]  or_out,
    input logic [3:0]  xor_out
);

    // and_out is the bitwise AND of the two active input nibbles.
    check_and_matches_bitwise_and: assert property (
        @(posedge clk) and_out == (in[3:0] & in[7:4])
    );

    // or_out is the bitwise OR of the two active input nibbles.
    check_or_matches_bitwise_or: assert property (
        @(posedge clk) or_out == (in[3:0] | in[7:4])
    );

    // xor_out is the bitwise XOR of the two active input nibbles.
    check_xor_matches_bitwise_xor: assert property (
        @(posedge clk) xor_out == (in[3:0] ^ in[7:4])
    );

    // Any bit set in and_out must also be set in or_out.
    check_and_is_subset_of_or: assert property (
        @(posedge clk) (and_out & ~or_out) == 4'b0000
    );

    // xor_out and and_out cannot share a set bit.
    check_xor_and_and_do_not_overlap: assert property (
        @(posedge clk) (xor_out & and_out) == 4'b0000
    );

    // xor_out equals or_out with the common set bits removed.
    check_xor_matches_or_minus_and: assert property (
        @(posedge clk) xor_out == (or_out & ~and_out)
    );

    // Equal input nibbles force xor_out low.
    check_equal_inputs_force_zero_xor: assert property (
        @(posedge clk) (in[3:0] == in[7:4]) |-> (xor_out == 4'b0000)
    );

    // A zero nibble on either side forces and_out low.
    check_zero_input_forces_zero_and: assert property (
        @(posedge clk) ((in[3:0] == 4'b0000) || (in[7:4] == 4'b0000)) |-> (and_out == 4'b0000)
    );

    // All-zero active inputs force all outputs low.
    check_all_zero_inputs_force_zero_outputs: assert property (
        @(posedge clk) (in[7:0] == 8'b00000000) |-> ((and_out == 4'b0000) && (or_out == 4'b0000) && (xor_out == 4'b0000))
    );

    // All-one active inputs force AND and OR high and XOR low.
    check_all_one_inputs_force_expected_outputs: assert property (
        @(posedge clk) (in[7:0] == 8'b11111111) |-> ((and_out == 4'b1111) && (or_out == 4'b1111) && (xor_out == 4'b0000))
    );

endmodule