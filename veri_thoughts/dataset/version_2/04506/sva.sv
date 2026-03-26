module adder_4bit_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    input logic [3:0] S,
    input logic Cout
);

    // The 5-bit result matches A + B + Cin.
    check_total_sum: assert property (
        @(posedge clk) {Cout, S} == ({1'b0, A} + {1'b0, B} + Cin)
    );

    // Bit 0 sum matches the first full adder XOR function.
    check_bit0_sum: assert property (
        @(posedge clk) S[0] == (A[0] ^ B[0] ^ Cin)
    );

    // Bit 1 sum uses the carry generated from bit 0.
    check_bit1_sum: assert property (
        @(posedge clk)
        S[1] == (A[1] ^ B[1] ^ ((A[0] & B[0]) | ((A[0] ^ B[0]) & Cin)))
    );

    // Bit 2 sum uses the carry generated from bit 1.
    check_bit2_sum: assert property (
        @(posedge clk)
        S[2] == (A[2] ^ B[2] ^
                 ((A[1] & B[1]) |
                  ((A[1] ^ B[1]) &
                   ((A[0] & B[0]) | ((A[0] ^ B[0]) & Cin)))))
    );

    // Bit 3 sum uses the carry generated from bit 2.
    check_bit3_sum: assert property (
        @(posedge clk)
        S[3] == (A[3] ^ B[3] ^
                 ((A[2] & B[2]) |
                  ((A[2] ^ B[2]) &
                   ((A[1] & B[1]) |
                    ((A[1] ^ B[1]) &
                     ((A[0] & B[0]) | ((A[0] ^ B[0]) & Cin)))))))
    );

    // Cout matches the final ripple carry from the MSB full adder.
    check_final_carry: assert property (
        @(posedge clk)
        Cout == ((A[3] & B[3]) |
                 ((A[3] ^ B[3]) &
                  ((A[2] & B[2]) |
                   ((A[2] ^ B[2]) &
                    ((A[1] & B[1]) |
                     ((A[1] ^ B[1]) &
                      ((A[0] & B[0]) | ((A[0] ^ B[0]) & Cin))))))))
    );

endmodule