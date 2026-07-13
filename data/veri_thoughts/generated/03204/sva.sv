module four_bit_adder_sva (
    input logic       clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       Cin,
    input logic [3:0] S,
    input logic       Cout
);

    function automatic logic fa_carry (
        input logic a,
        input logic b,
        input logic cin
    );
        fa_carry = (a & b) | (a & cin) | (b & cin);
    endfunction

    // Carry and sum must match 4-bit addition with carry-in.
    check_total_addition: assert property (
        @(posedge clk)
        {Cout, S} == ({1'b0, A} + {1'b0, B} + {4'b0, Cin})
    );

    // Bit 0 sum must match the first full-adder stage.
    check_sum_bit0: assert property (
        @(posedge clk)
        S[0] == (A[0] ^ B[0] ^ Cin)
    );

    // Bit 1 sum must use the carry from bit 0.
    check_sum_bit1: assert property (
        @(posedge clk)
        S[1] == (A[1] ^ B[1] ^ fa_carry(A[0], B[0], Cin))
    );

    // Bit 2 sum must use the carry propagated through bit 1.
    check_sum_bit2: assert property (
        @(posedge clk)
        S[2] == (A[2] ^ B[2] ^ fa_carry(A[1], B[1], fa_carry(A[0], B[0], Cin)))
    );

    // Bit 3 sum must use the carry propagated through bit 2.
    check_sum_bit3: assert property (
        @(posedge clk)
        S[3] == (A[3] ^ B[3] ^ fa_carry(A[2], B[2], fa_carry(A[1], B[1], fa_carry(A[0], B[0], Cin))))
    );

    // Cout must match the carry out of the MSB full-adder stage.
    check_final_carry: assert property (
        @(posedge clk)
        Cout == fa_carry(A[3], B[3], fa_carry(A[2], B[2], fa_carry(A[1], B[1], fa_carry(A[0], B[0], Cin))))
    );

endmodule