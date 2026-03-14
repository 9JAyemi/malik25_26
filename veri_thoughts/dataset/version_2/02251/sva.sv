module ripple_carry_adder_sva (
    input logic [2:0] A,
    input logic [2:0] B,
    input logic       Cin,
    input logic       clk,
    input logic [2:0] S,
    input logic       Cout
);
    // Clock: clk (posedge). No reset present in RTL. Sequential datapath: registered 3-bit ripple-carry add.

    // Full 4-bit sum correctness: {Cout,S} equals A + B + Cin.
    check_full_sum: assert property (
        @(posedge clk) {Cout, S} == ({1'b0, A} + {1'b0, B} + Cin)
    );

    // Bit0 sum is XOR of A0, B0, and Cin.
    check_bit0_sum_xor: assert property (
        @(posedge clk) S[0] == (A[0] ^ B[0] ^ Cin)
    );

    // Bit1 sum uses carry0 = (A0&B0)|(A0&Cin)|(B0&Cin).
    check_bit1_sum_xor_with_c0: assert property (
        @(posedge clk) S[1] == (A[1] ^ B[1] ^ ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin)))
    );

    // Bit2 sum uses carry1 = (A1&B1)|(A1&carry0)|(B1&carry0).
    check_bit2_sum_xor_with_c1: assert property (
        @(posedge clk) S[2] == (A[2] ^ B[2] ^
            (
                (A[1] & B[1]) |
                (A[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin))) |
                (B[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin)))
            )
        )
    );

    // Cout equals (A2&B2)|(A2&carry1)|(B2&carry1).
    check_cout_from_c1: assert property (
        @(posedge clk) Cout ==
            (
                (A[2] & B[2]) |
                (A[2] &
                    (
                        (A[1] & B[1]) |
                        (A[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin))) |
                        (B[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin)))
                    )
                ) |
                (B[2] &
                    (
                        (A[1] & B[1]) |
                        (A[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin))) |
                        (B[1] & ((A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin)))
                    )
                )
            )
    );

    // If inputs are stable over a cycle, outputs remain stable.
    check_outputs_stable_if_inputs_stable: assert property (
        @(posedge clk) $stable({A, B, Cin}) |-> $stable({S, Cout})
    );

    // If outputs changed over a cycle, at least one input changed.
    check_output_change_requires_input_change: assert property (
        @(posedge clk) $changed({S, Cout}) |-> !$stable({A, B, Cin})
    );

endmodule