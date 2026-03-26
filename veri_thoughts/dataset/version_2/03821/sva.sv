module adder_4bit_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic CIN,
    input logic [3:0] S,
    input logic COUT
);

    // Outputs match the RTL addition assignment.
    check_outputs_match_assigned_addition: assert property (
        @(posedge clk) {COUT, S} == (A + B + CIN)
    );

    // Sum matches the low 4 bits of the arithmetic result.
    check_sum_matches_low_4bits_of_extended_add: assert property (
        @(posedge clk) S == ({1'b0, A} + {1'b0, B} + CIN)[3:0]
    );

    // Zero inputs produce zero outputs.
    check_zero_inputs_produce_zero_outputs: assert property (
        @(posedge clk) (A == 4'h0 && B == 4'h0 && CIN == 1'b0) |-> (S == 4'h0 && COUT == 1'b0)
    );

    // With B and CIN low, the output passes A through.
    check_a_passthrough_when_b_and_cin_are_zero: assert property (
        @(posedge clk) (B == 4'h0 && CIN == 1'b0) |-> (S == A && COUT == 1'b0)
    );

    // With A and CIN low, the output passes B through.
    check_b_passthrough_when_a_and_cin_are_zero: assert property (
        @(posedge clk) (A == 4'h0 && CIN == 1'b0) |-> (S == B && COUT == 1'b0)
    );

    // With both operands low, CIN drives the least-significant sum bit.
    check_cin_only_when_a_and_b_are_zero: assert property (
        @(posedge clk) (A == 4'h0 && B == 4'h0) |-> (S == {3'b000, CIN} && COUT == 1'b0)
    );

    // No carry is produced when the full arithmetic result fits in 4 bits.
    check_no_carry_when_extended_sum_fits_in_4_bits: assert property (
        @(posedge clk) (({1'b0, A} + {1'b0, B} + CIN) < 5'd16) |-> (COUT == 1'b0)
    );

endmodule