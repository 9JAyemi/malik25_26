module adder_4bit_sva(
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    input logic [3:0] S,
    input logic Cout,
    input logic clk
);

    // Combinational adder sampled on an external assertion clock; no reset is present in the RTL.

    // Combined sum and carry-out match 4-bit addition with carry-in.
    check_total_sum_value: assert property (
        @(posedge clk)
        {Cout, S} == ({1'b0, A} + {1'b0, B} + {4'b0000, Cin})
    );

    // Bit 0 sum matches the first full-adder XOR equation.
    check_sum_bit0_logic: assert property (
        @(posedge clk)
        S[0] == (A[0] ^ B[0] ^ Cin)
    );

    // Bit 1 sum uses the carry generated from bit 0.
    check_sum_bit1_logic: assert property (
        @(posedge clk)
        S[1] == (
            A[1] ^ B[1] ^
            ((A[0] & B[0]) | (Cin & (A[0] ^ B[0])))
        )
    );

    // Bit 2 sum uses the ripple carry generated through bit 1.
    check_sum_bit2_logic: assert property (
        @(posedge clk)
        S[2] == (
            A[2] ^ B[2] ^
            (
                (A[1] & B[1]) |
                (((A[0] & B[0]) | (Cin & (A[0] ^ B[0]))) & (A[1] ^ B[1]))
            )
        )
    );

    // Bit 3 sum uses the ripple carry generated through bit 2.
    check_sum_bit3_logic: assert property (
        @(posedge clk)
        S[3] == (
            A[3] ^ B[3] ^
            (
                (A[2] & B[2]) |
                (
                    (
                        (A[1] & B[1]) |
                        (((A[0] & B[0]) | (Cin & (A[0] ^ B[0]))) & (A[1] ^ B[1]))
                    ) &
                    (A[2] ^ B[2])
                )
            )
        )
    );

    // Carry-out matches the final full-adder carry equation.
    check_carry_out_logic: assert property (
        @(posedge clk)
        Cout == (
            (A[3] & B[3]) |
            (
                (
                    (A[2] & B[2]) |
                    (
                        (
                            (A[1] & B[1]) |
                            (((A[0] & B[0]) | (Cin & (A[0] ^ B[0]))) & (A[1] ^ B[1]))
                        ) &
                        (A[2] ^ B[2])
                    )
                ) &
                (A[3] ^ B[3])
            )
        )
    );

endmodule