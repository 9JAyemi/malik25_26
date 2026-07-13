module four_bit_adder_sva (
    input logic       clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] S,
    input logic       COUT
);

    // Full 5-bit result must equal the unsigned sum of A and B.
    check_total_sum: assert property (
        @(posedge clk) {COUT, S} == ({1'b0, A} + {1'b0, B})
    );

    // Bit 0 sum must be the XOR of the input LSBs.
    check_lsb_sum: assert property (
        @(posedge clk) S[0] == (A[0] ^ B[0])
    );

    // Bit 1 sum must include the carry generated from bit 0.
    check_bit1_sum: assert property (
        @(posedge clk) S[1] == (A[1] ^ B[1] ^ (A[0] & B[0]))
    );

    // Carry-out must match the MSB of the extended addition.
    check_cout_matches_extended_sum: assert property (
        @(posedge clk) COUT == (({1'b0, A} + {1'b0, B})[4])
    );

    // A zero operand on A must pass B through with no carry-out.
    check_a_zero_passthrough: assert property (
        @(posedge clk) (A == 4'b0000) |-> ((S == B) && (COUT == 1'b0))
    );

    // A zero operand on B must pass A through with no carry-out.
    check_b_zero_passthrough: assert property (
        @(posedge clk) (B == 4'b0000) |-> ((S == A) && (COUT == 1'b0))
    );

    // Adding 8 and 8 must overflow to carry-out with a zero sum.
    check_msb_overflow_case: assert property (
        @(posedge clk) ((A == 4'h8) && (B == 4'h8)) |-> ((S == 4'h0) && (COUT == 1'b1))
    );

    // Adding 15 and 15 must produce 30 across carry-out and sum.
    check_full_scale_addition: assert property (
        @(posedge clk) ((A == 4'hF) && (B == 4'hF)) |-> ((S == 4'hE) && (COUT == 1'b1))
    );

    // Stable inputs must yield stable sampled outputs.
    check_stable_inputs_stable_outputs: assert property (
        @(posedge clk) $stable({A, B}) |-> $stable({COUT, S})
    );

endmodule