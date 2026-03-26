module four_bit_adder_sva(
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    input logic [3:0] S,
    input logic Cout
);

    // S[0] is the XOR of A[0], B[0], and Cin.
    check_sum_bit0: assert property (
        @($global_clock) S[0] == (A[0] ^ B[0] ^ Cin)
    );

    // S[1] is the XOR of A[1], B[1], and A[0]&B[0].
    check_sum_bit1: assert property (
        @($global_clock) S[1] == (A[1] ^ B[1] ^ (A[0] & B[0]))
    );

    // S[2] is the XOR of A[2], B[2], and A[1]&B[1].
    check_sum_bit2: assert property (
        @($global_clock) S[2] == (A[2] ^ B[2] ^ (A[1] & B[1]))
    );

    // S[3] is the XOR of A[3], B[3], and A[2]&B[2].
    check_sum_bit3: assert property (
        @($global_clock) S[3] == (A[3] ^ B[3] ^ (A[2] & B[2]))
    );

    // Cout is the OR of the three carry wires from bits 0 through 2.
    check_cout_equation: assert property (
        @($global_clock) Cout == ((A[0] & B[0]) | (A[1] & B[1]) | (A[2] & B[2]))
    );

endmodule