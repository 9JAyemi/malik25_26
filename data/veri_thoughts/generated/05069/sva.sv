module FourBitAdder_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    input logic [3:0] S,
    input logic Cout
);

    function automatic logic fa_cout(
        input logic a_i,
        input logic b_i,
        input logic cin_i
    );
        fa_cout = (a_i & b_i) | (b_i & cin_i) | (a_i & cin_i);
    endfunction

    // The 5-bit output matches A + B + Cin.
    check_total_sum: assert property (
        @(posedge clk) disable iff (1'b0)
        {Cout, S} == ({1'b0, A} + {1'b0, B} + Cin)
    );

    // Bit 0 sum matches the first full adder XOR equation.
    check_sum_bit0: assert property (
        @(posedge clk) disable iff (1'b0)
        S[0] == (A[0] ^ B[0] ^ Cin)
    );

    // Bit 1 sum uses the carry from bit 0.
    check_sum_bit1: assert property (
        @(posedge clk) disable iff (1'b0)
        S[1] == (A[1] ^ B[1] ^ fa_cout(A[0], B[0], Cin))
    );

    // Bit 2 sum uses the ripple carry from bits 0 and 1.
    check_sum_bit2: assert property (
        @(posedge clk) disable iff (1'b0)
        S[2] == (A[2] ^ B[2] ^ fa_cout(A[1], B[1], fa_cout(A[0], B[0], Cin)))
    );

    // Bit 3 sum uses the ripple carry from bits 0 through 2.
    check_sum_bit3: assert property (
        @(posedge clk) disable iff (1'b0)
        S[3] == (A[3] ^ B[3] ^ fa_cout(A[2], B[2], fa_cout(A[1], B[1], fa_cout(A[0], B[0], Cin))))
    );

    // Carry-out matches the final full adder carry equation.
    check_cout: assert property (
        @(posedge clk) disable iff (1'b0)
        Cout == fa_cout(A[3], B[3], fa_cout(A[2], B[2], fa_cout(A[1], B[1], fa_cout(A[0], B[0], Cin))))
    );

endmodule