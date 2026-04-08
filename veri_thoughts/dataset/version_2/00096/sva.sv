module four_bit_adder_sva (
    input logic       clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       C_in,
    input logic [3:0] S,
    input logic       C_out
);

function automatic logic fa_sum(
    input logic a,
    input logic b,
    input logic cin
);
    fa_sum = a ^ b ^ cin;
endfunction

function automatic logic fa_carry(
    input logic a,
    input logic b,
    input logic cin
);
    fa_carry = (a & b) | (cin & (a ^ b));
endfunction

// The 5-bit output matches A + B + C_in.
check_total_addition: assert property (
    @(posedge clk) disable iff (1'b0)
    {C_out, S} == ({1'b0, A} + {1'b0, B} + {4'b0000, C_in})
);

// Bit 0 sum matches the least-significant full adder.
check_sum_bit0: assert property (
    @(posedge clk) disable iff (1'b0)
    S[0] == fa_sum(A[0], B[0], C_in)
);

// Bit 1 sum uses the carry from bit 0.
check_sum_bit1: assert property (
    @(posedge clk) disable iff (1'b0)
    S[1] == fa_sum(A[1], B[1], fa_carry(A[0], B[0], C_in))
);

// Bit 2 sum uses the ripple carry from bits 0 and 1.
check_sum_bit2: assert property (
    @(posedge clk) disable iff (1'b0)
    S[2] == fa_sum(A[2], B[2], fa_carry(A[1], B[1], fa_carry(A[0], B[0], C_in)))
);

// Bit 3 sum uses the ripple carry from bits 0 through 2.
check_sum_bit3: assert property (
    @(posedge clk) disable iff (1'b0)
    S[3] == fa_sum(A[3], B[3], fa_carry(A[2], B[2], fa_carry(A[1], B[1], fa_carry(A[0], B[0], C_in))))
);

// Carry out matches the final full adder carry.
check_carry_out: assert property (
    @(posedge clk) disable iff (1'b0)
    C_out == fa_carry(A[3], B[3], fa_carry(A[2], B[2], fa_carry(A[1], B[1], fa_carry(A[0], B[0], C_in))))
);

// Adding zero on B with no carry-in preserves A.
check_zero_b_no_carry: assert property (
    @(posedge clk) disable iff (1'b0)
    (B == 4'b0000 && C_in == 1'b0) |-> ({C_out, S} == {1'b0, A})
);

// Adding zero on A with no carry-in preserves B.
check_zero_a_no_carry: assert property (
    @(posedge clk) disable iff (1'b0)
    (A == 4'b0000 && C_in == 1'b0) |-> ({C_out, S} == {1'b0, B})
);

// Zero operands pass carry-in only to the least-significant sum bit.
check_zero_inputs: assert property (
    @(posedge clk) disable iff (1'b0)
    (A == 4'b0000 && B == 4'b0000) |-> (S == {3'b000, C_in} && C_out == 1'b0)
);

// All ones plus carry-in produces the maximum 5-bit result.
check_max_addition: assert property (
    @(posedge clk) disable iff (1'b0)
    (A == 4'hF && B == 4'hF && C_in == 1'b1) |-> (S == 4'hF && C_out == 1'b1)
);

endmodule