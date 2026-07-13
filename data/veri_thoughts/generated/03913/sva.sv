module four_bit_adder_sva(
    input logic       clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       Cin,
    input logic [3:0] S,
    input logic       Cout
);

    // Full 5-bit result must match A + B + Cin.
    check_total_sum: assert property (
        @(posedge clk)
        {Cout, S} == ({1'b0, A} + {1'b0, B} + Cin)
    );

    // Bit 0 sum must match the first full-adder XOR equation.
    check_sum_bit0: assert property (
        @(posedge clk)
        S[0] == (A[0] ^ B[0] ^ Cin)
    );

    // Bit 1 sum must use the ripple carry from bit 0.
    check_sum_bit1: assert property (
        @(posedge clk)
        S[1] == (A[1] ^ B[1] ^ ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin)))
    );

    // Bit 2 sum must use the ripple carry from bit 1.
    check_sum_bit2: assert property (
        @(posedge clk)
        S[2] == (
            A[2] ^ B[2] ^ (
                (A[1] & B[1]) |
                (A[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin))) |
                (B[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin)))
            )
        )
    );

    // Bit 3 sum must use the ripple carry from bit 2.
    check_sum_bit3: assert property (
        @(posedge clk)
        S[3] == (
            A[3] ^ B[3] ^ (
                (A[2] & B[2]) |
                (A[2] & (
                    (A[1] & B[1]) |
                    (A[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin))) |
                    (B[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin)))
                )) |
                (B[2] & (
                    (A[1] & B[1]) |
                    (A[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin))) |
                    (B[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin)))
                ))
            )
        )
    );

    // Carry out must match the final full-adder carry equation.
    check_cout_equation: assert property (
        @(posedge clk)
        Cout == (
            (A[3] & B[3]) |
            (A[3] & (
                (A[2] & B[2]) |
                (A[2] & (
                    (A[1] & B[1]) |
                    (A[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin))) |
                    (B[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin)))
                )) |
                (B[2] & (
                    (A[1] & B[1]) |
                    (A[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin))) |
                    (B[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin)))
                ))
            )) |
            (B[3] & (
                (A[2] & B[2]) |
                (A[2] & (
                    (A[1] & B[1]) |
                    (A[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin))) |
                    (B[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin)))
                )) |
                (B[2] & (
                    (A[1] & B[1]) |
                    (A[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin))) |
                    (B[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin)))
                ))
            ))
        )
    );

    // Zero inputs with zero carry-in must produce zero outputs.
    check_zero_addition: assert property (
        @(posedge clk)
        ((A == 4'b0000) && (B == 4'b0000) && (Cin == 1'b0)) |-> ((S == 4'b0000) && (Cout == 1'b0))
    );

    // With B and Cin at zero, the sum must pass A through.
    check_pass_a_when_b_zero: assert property (
        @(posedge clk)
        ((B == 4'b0000) && (Cin == 1'b0)) |-> ((S == A) && (Cout == 1'b0))
    );

    // With A and Cin at zero, the sum must pass B through.
    check_pass_b_when_a_zero: assert property (
        @(posedge clk)
        ((A == 4'b0000) && (Cin == 1'b0)) |-> ((S == B) && (Cout == 1'b0))
    );

    // Arithmetic overflow must set Cout.
    check_overflow_sets_cout: assert property (
        @(posedge clk)
        (({1'b0, A} + {1'b0, B} + Cin) > 5'd15) |-> (Cout == 1'b1)
    );

    // No arithmetic overflow must clear Cout.
    check_no_overflow_clears_cout: assert property (
        @(posedge clk)
        (({1'b0, A} + {1'b0, B} + Cin) <= 5'd15) |-> (Cout == 1'b0)
    );

endmodule