module four_bit_adder_sva (
    input logic        clk,
    input logic [3:0]  A,
    input logic [3:0]  B,
    input logic        Cin,
    input logic [3:0]  S,
    input logic        Cout
);

    function automatic logic fa_carry (
        input logic a,
        input logic b,
        input logic cin
    );
        fa_carry = (a & b) | (cin & (a ^ b));
    endfunction

    // The 5-bit result must equal A + B + Cin.
    check_total_sum_matches_addition: assert property (
        @(posedge clk) {Cout, S} == ({1'b0, A} + {1'b0, B} + Cin)
    );

    // Bit 0 sum must match the first full-adder XOR equation.
    check_bit0_sum_equation: assert property (
        @(posedge clk) S[0] == (A[0] ^ B[0] ^ Cin)
    );

    // Bit 1 sum must use the carry from bit 0.
    check_bit1_sum_equation: assert property (
        @(posedge clk) S[1] == (A[1] ^ B[1] ^ fa_carry(A[0], B[0], Cin))
    );

    // Bit 2 sum must use the carry propagated through bits 0 and 1.
    check_bit2_sum_equation: assert property (
        @(posedge clk) S[2] == (A[2] ^ B[2] ^ fa_carry(A[1], B[1], fa_carry(A[0], B[0], Cin)))
    );

    // Bit 3 sum must use the carry propagated through bits 0 to 2.
    check_bit3_sum_equation: assert property (
        @(posedge clk) S[3] == (A[3] ^ B[3] ^ fa_carry(A[2], B[2], fa_carry(A[1], B[1], fa_carry(A[0], B[0], Cin))))
    );

    // Carry out must match the final full-adder carry equation.
    check_cout_equation: assert property (
        @(posedge clk) Cout == fa_carry(A[3], B[3], fa_carry(A[2], B[2], fa_carry(A[1], B[1], fa_carry(A[0], B[0], Cin))))
    );

endmodule