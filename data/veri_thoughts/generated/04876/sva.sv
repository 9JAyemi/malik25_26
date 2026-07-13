module four_bit_adder_sva (
    input logic       clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       Cin,
    input logic [3:0] C,
    input logic       Cout
);

    // Output bus and carry must equal A + B + Cin.
    check_total_sum: assert property (
        @(posedge clk) {Cout, C} == ({1'b0, A} + {1'b0, B} + {4'b0000, Cin})
    );

    // Sum bit 0 must implement the first full-adder sum.
    check_sum_bit0: assert property (
        @(posedge clk) C[0] == (A[0] ^ B[0] ^ Cin)
    );

    // Sum bit 1 must use the carry from bit 0.
    check_sum_bit1: assert property (
        @(posedge clk) C[1] == (A[1] ^ B[1] ^ ((A[0] & B[0]) | (Cin & (A[0] ^ B[0]))))
    );

    // Sum bit 2 must use the ripple carry from bits 0 and 1.
    check_sum_bit2: assert property (
        @(posedge clk)
        C[2] == (A[2] ^ B[2] ^
                 ((A[1] & B[1]) |
                  (((A[0] & B[0]) | (Cin & (A[0] ^ B[0]))) & (A[1] ^ B[1]))))
    );

    // Sum bit 3 must use the ripple carry from bits 0 through 2.
    check_sum_bit3: assert property (
        @(posedge clk)
        C[3] == (A[3] ^ B[3] ^
                 ((A[2] & B[2]) |
                  ((((A[1] & B[1]) |
                     (((A[0] & B[0]) | (Cin & (A[0] ^ B[0]))) & (A[1] ^ B[1])))) &
                   (A[2] ^ B[2])))))
    );

    // Cout must be the final carry of the 4-bit ripple chain.
    check_final_carry: assert property (
        @(posedge clk)
        Cout == ((A[3] & B[3]) |
                 ((((A[2] & B[2]) |
                    ((((A[1] & B[1]) |
                       (((A[0] & B[0]) | (Cin & (A[0] ^ B[0]))) & (A[1] ^ B[1])))) &
                     (A[2] ^ B[2])))) &
                  (A[3] ^ B[3]))))
    );

endmodule