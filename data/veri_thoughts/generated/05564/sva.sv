module four_bit_adder_assertions (
    input logic       clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       C_in,
    input logic [3:0] S,
    input logic       C_out
);

    function automatic logic fa_carry (
        input logic a,
        input logic b,
        input logic cin
    );
        fa_carry = (a & b) | (a & cin) | (b & cin);
    endfunction

    // Overall sum and carry match the 4-bit addition result.
    check_total_sum: assert property (
        @(posedge clk) {C_out, S} == ({1'b0, A} + {1'b0, B} + {4'b0, C_in})
    );

    // Bit 0 sum matches the first full-adder stage.
    check_bit0_sum: assert property (
        @(posedge clk) S[0] == (A[0] ^ B[0] ^ C_in)
    );

    // Bit 1 sum uses the carry from bit 0.
    check_bit1_sum: assert property (
        @(posedge clk) S[1] == (A[1] ^ B[1] ^ fa_carry(A[0], B[0], C_in))
    );

    // Bit 2 sum uses the carry from bit 1.
    check_bit2_sum: assert property (
        @(posedge clk) S[2] == (A[2] ^ B[2] ^ fa_carry(A[1], B[1], fa_carry(A[0], B[0], C_in)))
    );

    // Bit 3 sum uses the carry from bit 2.
    check_bit3_sum: assert property (
        @(posedge clk) S[3] == (A[3] ^ B[3] ^ fa_carry(A[2], B[2], fa_carry(A[1], B[1], fa_carry(A[0], B[0], C_in))))
    );

    // Carry-out matches the last full-adder carry equation.
    check_final_carry: assert property (
        @(posedge clk) C_out == fa_carry(A[3], B[3], fa_carry(A[2], B[2], fa_carry(A[1], B[1], fa_carry(A[0], B[0], C_in))))
    );

endmodule