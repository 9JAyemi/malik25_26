module four_bit_adder_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    input logic [3:0] S,
    input logic Cout
);

    // S[0] matches the RTL XOR equation.
    check_sum_bit0_equation: assert property (
        @(posedge clk) S[0] == (A[0] ^ B[0] ^ Cin)
    );

    // S[1] matches the RTL XOR equation using the carry from bit 0.
    check_sum_bit1_equation: assert property (
        @(posedge clk) S[1] == (A[1] ^ B[1] ^ ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin)))
    );

    // S[2] matches the RTL XOR equation using the carry from bit 1.
    check_sum_bit2_equation: assert property (
        @(posedge clk) S[2] == (A[2] ^ B[2] ^
            ((A[1] & B[1]) |
             (A[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin))) |
             (B[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin)))))
    );

    // S[3] matches the RTL XOR equation using the carry from bit 2.
    check_sum_bit3_equation: assert property (
        @(posedge clk) S[3] == (A[3] ^ B[3] ^
            ((A[2] & B[2]) |
             (A[2] & ((A[1] & B[1]) |
                      (A[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin))) |
                      (B[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin))))) |
             (B[2] & ((A[1] & B[1]) |
                      (A[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin))) |
                      (B[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin)))))))
    );

    // Cout matches the RTL carry-out equation.
    check_cout_equation: assert property (
        @(posedge clk) Cout == ((A[3] & B[3]) |
                               (A[3] & ((A[2] & B[2]) |
                                        (A[2] & ((A[1] & B[1]) |
                                                 (A[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin))) |
                                                 (B[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin))))) |
                                        (B[2] & ((A[1] & B[1]) |
                                                 (A[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin))) |
                                                 (B[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin))))))) |
                               (B[3] & ((A[2] & B[2]) |
                                        (A[2] & ((A[1] & B[1]) |
                                                 (A[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin))) |
                                                 (B[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin))))) |
                                        (B[2] & ((A[1] & B[1]) |
                                                 (A[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin))) |
                                                 (B[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin)))))))))
    );

    // The concatenated output {Cout,S} matches the 5-bit addition of A, B, and Cin.
    check_full_adder_result: assert property (
        @(posedge clk) {Cout, S} == ({1'b0, A} + {1'b0, B} + {4'b0000, Cin})
    );

endmodule