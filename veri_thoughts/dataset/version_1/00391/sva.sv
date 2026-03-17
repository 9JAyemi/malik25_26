module four_bit_adder_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    input logic [3:0] S,
    input logic Cout
);

    function automatic logic fa_carry (
        input logic a,
        input logic b,
        input logic cin
    );
        fa_carry = (a & b) | ((a ^ b) & cin);
    endfunction

    // The 5-bit output matches A + B + Cin.
    check_total_result: assert property (
        @($global_clock) {Cout, S} == ({1'b0, A} + {1'b0, B} + Cin)
    );

    // Sum bit 0 is the XOR of A[0], B[0], and Cin.
    check_sum_bit0: assert property (
        @($global_clock) S[0] == (A[0] ^ B[0] ^ Cin)
    );

    // Sum bit 1 uses the carry out of bit 0.
    check_sum_bit1: assert property (
        @($global_clock) S[1] == (A[1] ^ B[1] ^ fa_carry(A[0], B[0], Cin))
    );

    // Sum bit 2 uses the carry out of bit 1.
    check_sum_bit2: assert property (
        @($global_clock) S[2] == (A[2] ^ B[2] ^ fa_carry(A[1], B[1], fa_carry(A[0], B[0], Cin)))
    );

    // Sum bit 3 uses the carry out of bit 2.
    check_sum_bit3: assert property (
        @($global_clock) S[3] == (A[3] ^ B[3] ^ fa_carry(A[2], B[2], fa_carry(A[1], B[1], fa_carry(A[0], B[0], Cin))))
    );

    // Cout is the final carry out of the ripple chain.
    check_final_carry: assert property (
        @($global_clock) Cout == fa_carry(A[3], B[3], fa_carry(A[2], B[2], fa_carry(A[1], B[1], fa_carry(A[0], B[0], Cin))))
    );

endmodule