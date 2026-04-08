module four_bit_adder_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    input logic [3:0] Sum,
    input logic Cout
);

    // Sum[0] matches the bit-0 full-adder equation.
    check_sum_bit0_equation: assert property (
        @(posedge clk) disable iff (1'b0)
            Sum[0] == (A[0] ^ B[0] ^ Cin)
    );

    // Sum[1] matches the bit-1 ripple-carry equation.
    check_sum_bit1_equation: assert property (
        @(posedge clk) disable iff (1'b0)
            Sum[1] == (A[1] ^ B[1] ^
                       ((A[0] & B[0]) | ((A[0] ^ B[0]) & Cin)))
    );

    // Sum[2] matches the bit-2 ripple-carry equation.
    check_sum_bit2_equation: assert property (
        @(posedge clk) disable iff (1'b0)
            Sum[2] == (A[2] ^ B[2] ^
                       ((A[1] & B[1]) |
                        ((A[1] ^ B[1]) &
                         ((A[0] & B[0]) | ((A[0] ^ B[0]) & Cin)))))
    );

    // Sum[3] matches the bit-3 ripple-carry equation.
    check_sum_bit3_equation: assert property (
        @(posedge clk) disable iff (1'b0)
            Sum[3] == (A[3] ^ B[3] ^
                       ((A[2] & B[2]) |
                        ((A[2] ^ B[2]) &
                         ((A[1] & B[1]) |
                          ((A[1] ^ B[1]) &
                           ((A[0] & B[0]) | ((A[0] ^ B[0]) & Cin)))))))
    );

    // Cout matches the final ripple-carry equation.
    check_cout_equation: assert property (
        @(posedge clk) disable iff (1'b0)
            Cout == ((A[3] & B[3]) |
                     ((A[3] ^ B[3]) &
                      ((A[2] & B[2]) |
                       ((A[2] ^ B[2]) &
                        ((A[1] & B[1]) |
                         ((A[1] ^ B[1]) &
                          ((A[0] & B[0]) | ((A[0] ^ B[0]) & Cin))))))))
    );

    // The outputs match 5-bit addition of A, B, and Cin.
    check_total_addition: assert property (
        @(posedge clk) disable iff (1'b0)
            {Cout, Sum} == ({1'b0, A} + {1'b0, B} + {4'b0000, Cin})
    );

endmodule