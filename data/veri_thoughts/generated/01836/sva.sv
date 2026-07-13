module four_bit_adder_sva (
    input logic clk,          // SVA sample clock (RTL is purely combinational; no reset)
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    input logic [3:0] S,
    input logic Cout
);
    // Full 5-bit sum must equal zero-extended A+B+Cin.
    check_sum_matches_arithmetic: assert property (
        @(posedge clk) disable iff (1'b0)
        {Cout, S} == ({1'b0, A} + {1'b0, B} + {4'b0, Cin})
    );

    // Bit0 sum is XOR of A[0], B[0], and Cin.
    check_sum_bit0_xor: assert property (
        @(posedge clk) disable iff (1'b0)
        S[0] == (A[0] ^ B[0] ^ Cin)
    );

    // Bit1 sum equals XOR with carry from bit0.
    check_sum_bit1_xor_with_c1: assert property (
        @(posedge clk) disable iff (1'b0)
        S[1] == (A[1] ^ B[1] ^ ( (A[0] & B[0]) | (Cin & (A[0] ^ B[0])) ))
    );

    // Bit2 sum equals XOR with carry from bit1.
    check_sum_bit2_xor_with_c2: assert property (
        @(posedge clk) disable iff (1'b0)
        S[2] == (A[2] ^ B[2] ^ (
                    (A[1] & B[1]) |
                    ( ((A[0] & B[0]) | (Cin & (A[0] ^ B[0]))) & (A[1] ^ B[1]) )
                ))
    );

    // Bit3 sum equals XOR with carry from bit2.
    check_sum_bit3_xor_with_c3: assert property (
        @(posedge clk) disable iff (1'b0)
        S[3] == (A[3] ^ B[3] ^ (
                    (A[2] & B[2]) |
                    ( ( (A[1] & B[1]) |
                        ( ((A[0] & B[0]) | (Cin & (A[0] ^ B[0]))) & (A[1] ^ B[1]) )
                      ) & (A[2] ^ B[2]) )
                ))
    );

    // Carry-out equals ripple-carry chain through all bits.
    check_cout_matches_ripple: assert property (
        @(posedge clk) disable iff (1'b0)
        Cout == (
            (A[3] & B[3]) |
            ( (
                (A[2] & B[2]) |
                ( ( (A[1] & B[1]) |
                    ( ((A[0] & B[0]) | (Cin & (A[0] ^ B[0]))) & (A[1] ^ B[1]) )
                  ) & (A[2] ^ B[2]) )
              ) & (A[3] ^ B[3]) )
        )
    );

    // If inputs do not change, outputs must not change.
    check_outputs_stable_when_inputs_stable: assert property (
        @(posedge clk) disable iff (1'b0)
        ($stable(A) && $stable(B) && $stable(Cin)) |-> ($stable(S) && $stable(Cout))
    );

    // 0 + 0 + 0 -> S=0, Cout=0.
    check_zero_plus_zero_no_carry: assert property (
        @(posedge clk) disable iff (1'b0)
        ((A == 4'b0000) && (B == 4'b0000) && (Cin == 1'b0)) |-> ((S == 4'b0000) && (Cout == 1'b0))
    );

    // 0 + 0 + 1 -> S=1, Cout=0.
    check_zero_plus_zero_with_cin: assert property (
        @(posedge clk) disable iff (1'b0)
        ((A == 4'b0000) && (B == 4'b0000) && (Cin == 1'b1)) |-> ((S == 4'b0001) && (Cout == 1'b0))
    );

    // A + ~A + 0 -> S=4'hF, Cout=0.
    check_complement_no_cin_saturates: assert property (
        @(posedge clk) disable iff (1'b0)
        ((B == ~A) && (Cin == 1'b0)) |-> ((S == 4'hF) && (Cout == 1'b0))
    );

    // A + ~A + 1 -> S=0, Cout=1.
    check_complement_with_cin_wraps: assert property (
        @(posedge clk) disable iff (1'b0)
        ((B == ~A) && (Cin == 1'b1)) |-> ((S == 4'h0) && (Cout == 1'b1))
    );
endmodule