module adder_4bit_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    input logic [3:0] S,
    input logic Cout
);

    function automatic logic carry_f (
        input logic a,
        input logic b,
        input logic cin_i
    );
        carry_f = (a & b) | (cin_i & (a ^ b));
    endfunction

    // Bit 0 sum matches the first full adder equation.
    check_sum_bit0_equation: assert property (
        @(posedge clk) S[0] == (A[0] ^ B[0] ^ Cin)
    );

    // Bit 1 sum matches the ripple-carry full adder equation.
    check_sum_bit1_equation: assert property (
        @(posedge clk) S[1] == (A[1] ^ B[1] ^ carry_f(A[0], B[0], Cin))
    );

    // Bit 2 sum matches the ripple-carry full adder equation.
    check_sum_bit2_equation: assert property (
        @(posedge clk) S[2] == (A[2] ^ B[2] ^ carry_f(A[1], B[1], carry_f(A[0], B[0], Cin)))
    );

    // Bit 3 sum matches the ripple-carry full adder equation.
    check_sum_bit3_equation: assert property (
        @(posedge clk) S[3] == (A[3] ^ B[3] ^ carry_f(A[2], B[2], carry_f(A[1], B[1], carry_f(A[0], B[0], Cin))))
    );

    // Carry out matches the last full adder carry equation.
    check_carry_out_equation: assert property (
        @(posedge clk) Cout == carry_f(A[3], B[3], carry_f(A[2], B[2], carry_f(A[1], B[1], carry_f(A[0], B[0], Cin))))
    );

    // The concatenated result matches 4-bit addition with carry in.
    check_full_result_equation: assert property (
        @(posedge clk) {Cout, S} == ({1'b0, A} + {1'b0, B} + {{4{1'b0}}, Cin})
    );

endmodule