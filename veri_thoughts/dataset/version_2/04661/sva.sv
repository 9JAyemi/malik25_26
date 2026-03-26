module full_adder_4bit_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic CIN,
    input logic [3:0] SUM,
    input logic COUT,
    input logic clk
);

    function automatic logic fa_carry (
        input logic a,
        input logic b,
        input logic cin_i
    );
        fa_carry = (a & b) | (a & cin_i) | (b & cin_i);
    endfunction

    // Outputs equal the 5-bit sum of A, B, and CIN.
    check_total_addition: assert property (
        @(posedge clk) {COUT, SUM} == ({1'b0, A} + {1'b0, B} + CIN)
    );

    // SUM[0] is the XOR of the LSB inputs and carry-in.
    check_sum_bit0: assert property (
        @(posedge clk) SUM[0] == (A[0] ^ B[0] ^ CIN)
    );

    // SUM[1] uses the carry generated from bit 0.
    check_sum_bit1: assert property (
        @(posedge clk) SUM[1] == (A[1] ^ B[1] ^ fa_carry(A[0], B[0], CIN))
    );

    // SUM[2] uses the carry generated from bit 1.
    check_sum_bit2: assert property (
        @(posedge clk) SUM[2] == (A[2] ^ B[2] ^ fa_carry(A[1], B[1], fa_carry(A[0], B[0], CIN)))
    );

    // SUM[3] uses the carry generated from bit 2.
    check_sum_bit3: assert property (
        @(posedge clk) SUM[3] == (A[3] ^ B[3] ^ fa_carry(A[2], B[2], fa_carry(A[1], B[1], fa_carry(A[0], B[0], CIN))))
    );

    // COUT is the carry generated from the MSB addition.
    check_cout_formula: assert property (
        @(posedge clk) COUT == fa_carry(A[3], B[3], fa_carry(A[2], B[2], fa_carry(A[1], B[1], fa_carry(A[0], B[0], CIN))))
    );

    // Zero inputs with no carry-in produce a zero result.
    check_zero_case: assert property (
        @(posedge clk) (A == 4'h0 && B == 4'h0 && CIN == 1'b0) |-> ({COUT, SUM} == 5'h00)
    );

    // Carry-in propagates through all one bits to produce a carry-out.
    check_full_carry_chain: assert property (
        @(posedge clk) (A == 4'hF && B == 4'h0 && CIN == 1'b1) |-> ({COUT, SUM} == 5'h10)
    );

endmodule