module four_bit_adder_sva(
    input logic       clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       Cin,
    input logic [3:0] S,
    input logic       Cout
);

    function automatic logic fa_sum(input logic x, input logic y, input logic z);
        fa_sum = x ^ y ^ z;
    endfunction

    function automatic logic fa_carry(input logic x, input logic y, input logic z);
        fa_carry = (x & y) | (x & z) | (y & z);
    endfunction

    // Bit 0 sum matches a full adder.
    check_bit0_sum: assert property (
        @(posedge clk) S[0] == fa_sum(A[0], B[0], Cin)
    );

    // Bit 1 sum uses the carry from bit 0.
    check_bit1_sum: assert property (
        @(posedge clk) S[1] == fa_sum(A[1], B[1], fa_carry(A[0], B[0], Cin))
    );

    // Bit 2 sum uses the ripple carry from bit 1.
    check_bit2_sum: assert property (
        @(posedge clk) S[2] == fa_sum(A[2], B[2],
                                      fa_carry(A[1], B[1], fa_carry(A[0], B[0], Cin)))
    );

    // Bit 3 sum uses the ripple carry from bit 2.
    check_bit3_sum: assert property (
        @(posedge clk) S[3] == fa_sum(A[3], B[3],
                                      fa_carry(A[2], B[2],
                                               fa_carry(A[1], B[1], fa_carry(A[0], B[0], Cin))))
    );

    // Carry out matches the final full-adder carry.
    check_cout_ripple: assert property (
        @(posedge clk) Cout == fa_carry(A[3], B[3],
                                        fa_carry(A[2], B[2],
                                                 fa_carry(A[1], B[1], fa_carry(A[0], B[0], Cin))))
    );

    // Combined outputs equal the 5-bit arithmetic sum.
    check_total_sum: assert property (
        @(posedge clk) {Cout, S} == ({1'b0, A} + {1'b0, B} + Cin)
    );

    // Adding zero with no carry-in passes A through unchanged.
    check_add_zero_to_a: assert property (
        @(posedge clk) (B == 4'h0 && Cin == 1'b0) |-> ({Cout, S} == {1'b0, A})
    );

    // Adding zero with no carry-in passes B through unchanged.
    check_add_zero_to_b: assert property (
        @(posedge clk) (A == 4'h0 && Cin == 1'b0) |-> ({Cout, S} == {1'b0, B})
    );

    // Zero operands produce only the carry-in in the result.
    check_zero_operands_with_cin: assert property (
        @(posedge clk) (A == 4'h0 && B == 4'h0) |-> (S == {3'b000, Cin} && Cout == 1'b0)
    );

    // Stable sampled inputs keep the sampled outputs stable.
    check_stable_inputs_stable_outputs: assert property (
        @(posedge clk) ($stable(A) && $stable(B) && $stable(Cin)) |-> $stable({Cout, S})
    );

endmodule