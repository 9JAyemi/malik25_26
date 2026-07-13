module four_bit_adder_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    input logic [3:0] S,
    input logic Cout
);

    // The concatenated carry and sum match the 5-bit arithmetic result.
    check_full_result_matches_addition: assert property (
        @($global_clock)
        {Cout, S} == ({1'b0, A} + {1'b0, B} + {4'b0000, Cin})
    );

    // Bit 0 sum implements a full-adder sum with Cin.
    check_sum_bit0_equation: assert property (
        @($global_clock)
        S[0] == (A[0] ^ B[0] ^ Cin)
    );

    // Bit 1 sum uses the ripple carry generated from bit 0.
    check_sum_bit1_equation: assert property (
        @($global_clock)
        S[1] == (A[1] ^ B[1] ^ ((A[0] & B[0]) | (Cin & (A[0] ^ B[0]))))
    );

    // Bit 2 sum uses the ripple carry generated from bits 0 and 1.
    check_sum_bit2_equation: assert property (
        @($global_clock)
        S[2] == (A[2] ^ B[2] ^
                 ((A[1] & B[1]) |
                  (((A[0] & B[0]) | (Cin & (A[0] ^ B[0]))) & (A[1] ^ B[1]))))
    );

    // Bit 3 sum uses the ripple carry generated from bits 0 through 2.
    check_sum_bit3_equation: assert property (
        @($global_clock)
        S[3] == (A[3] ^ B[3] ^
                 ((A[2] & B[2]) |
                  (((A[1] & B[1]) |
                    (((A[0] & B[0]) | (Cin & (A[0] ^ B[0]))) & (A[1] ^ B[1]))) &
                   (A[2] ^ B[2]))))
    );

    // Cout implements the final ripple-carry equation from the MSB stage.
    check_cout_equation: assert property (
        @($global_clock)
        Cout == ((A[3] & B[3]) |
                 (((A[2] & B[2]) |
                   (((A[1] & B[1]) |
                     (((A[0] & B[0]) | (Cin & (A[0] ^ B[0]))) & (A[1] ^ B[1]))) &
                    (A[2] ^ B[2]))) &
                  (A[3] ^ B[3])))
    );

endmodule