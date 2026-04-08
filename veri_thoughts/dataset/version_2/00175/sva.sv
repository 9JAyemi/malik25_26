module Adder4_sva (
    input logic       clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       Cin,
    input logic [3:0] S,
    input logic       Cout
);

    function automatic logic carry3(input logic x, input logic y, input logic z);
        carry3 = (x & y) | (x & z) | (y & z);
    endfunction

    // Full 5-bit output matches 4-bit addition with carry-in.
    check_total_sum: assert property (
        @(posedge clk) {Cout, S} == ({1'b0, A} + {1'b0, B} + Cin)
    );

    // Bit 0 sum is the XOR of A[0], B[0], and Cin.
    check_sum_bit0: assert property (
        @(posedge clk) S[0] == (A[0] ^ B[0] ^ Cin)
    );

    // Bit 1 sum uses the carry generated from bit 0.
    check_sum_bit1: assert property (
        @(posedge clk) S[1] == (A[1] ^ B[1] ^ carry3(A[0], B[0], Cin))
    );

    // Bit 2 sum uses the carry propagated through bit 1.
    check_sum_bit2: assert property (
        @(posedge clk) S[2] == (A[2] ^ B[2] ^ carry3(A[1], B[1], carry3(A[0], B[0], Cin)))
    );

    // Bit 3 sum uses the carry propagated through bit 2.
    check_sum_bit3: assert property (
        @(posedge clk) S[3] == (A[3] ^ B[3] ^ carry3(A[2], B[2], carry3(A[1], B[1], carry3(A[0], B[0], Cin))))
    );

    // Cout is the final carry from the MSB full adder.
    check_carry_out: assert property (
        @(posedge clk) Cout == carry3(A[3], B[3], carry3(A[2], B[2], carry3(A[1], B[1], carry3(A[0], B[0], Cin))))
    );

    // Adding zero on B with Cin low passes A through unchanged.
    check_pass_a_when_b_zero: assert property (
        @(posedge clk) ((B == 4'b0000) && (Cin == 1'b0)) |-> ({Cout, S} == {1'b0, A})
    );

    // Adding zero on A with Cin low passes B through unchanged.
    check_pass_b_when_a_zero: assert property (
        @(posedge clk) ((A == 4'b0000) && (Cin == 1'b0)) |-> ({Cout, S} == {1'b0, B})
    );

    // With B at zero and Cin high, the adder increments A by one.
    check_increment_when_b_zero_and_cin_one: assert property (
        @(posedge clk) ((B == 4'b0000) && (Cin == 1'b1)) |-> ({Cout, S} == ({1'b0, A} + 5'd1))
    );

    // The maximum input case produces all ones across Cout and S.
    check_full_overflow_case: assert property (
        @(posedge clk) ((A == 4'hF) && (B == 4'hF) && (Cin == 1'b1)) |-> ({Cout, S} == 5'h1F)
    );

endmodule