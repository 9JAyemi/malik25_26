module four_bit_adder_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    input logic [3:0] S,
    input logic Cout
);
    // Carry function for a single bit full adder stage.
    function automatic logic carr(input logic a, input logic b, input logic c_in);
        carr = (a & b) | (c_in & (a ^ b));
    endfunction

    // Sum bit 0 equals XOR of A[0], B[0], and Cin.
    check_sum0_xor: assert property (
        @(posedge clk) S[0] == (A[0] ^ B[0] ^ Cin)
    );

    // Sum bit 1 equals XOR of A[1], B[1], and carry from bit 0.
    check_sum1_xor_with_carry: assert property (
        @(posedge clk) S[1] == (A[1] ^ B[1] ^ carr(A[0], B[0], Cin))
    );

    // Sum bit 2 equals XOR of A[2], B[2], and carry from bit 1.
    check_sum2_xor_with_carry: assert property (
        @(posedge clk) S[2] == (A[2] ^ B[2] ^ carr(A[1], B[1], carr(A[0], B[0], Cin)))
    );

    // Sum bit 3 equals XOR of A[3], B[3], and carry from bit 2.
    check_sum3_xor_with_carry: assert property (
        @(posedge clk) S[3] == (A[3] ^ B[3] ^ carr(A[2], B[2], carr(A[1], B[1], carr(A[0], B[0], Cin))))
    );

    // Cout equals carry from the MSB stage.
    check_cout_ripple: assert property (
        @(posedge clk) Cout == carr(A[3], B[3], carr(A[2], B[2], carr(A[1], B[1], carr(A[0], B[0], Cin))))
    );

    // The 5-bit result {Cout,S} equals A + B + Cin.
    check_5bit_sum_matches: assert property (
        @(posedge clk) {Cout, S} == (A + B + Cin)
    );
endmodule