module ripple_carry_adder_sva (
    input logic       clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       Cin,
    input logic [3:0] S,
    input logic       Cout
);

    // The 5-bit output must equal A + B + Cin.
    check_total_sum: assert property (
        @(posedge clk) disable iff (1'b0)
        {Cout, S} == ({1'b0, A} + {1'b0, B} + Cin)
    );

    // Sum bit 0 must match the least-significant full-adder equation.
    check_sum_bit0: assert property (
        @(posedge clk) disable iff (1'b0)
        S[0] == (A[0] ^ B[0] ^ Cin)
    );

    // Sum bit 1 must include carry propagation from bit 0.
    check_sum_bit1: assert property (
        @(posedge clk) disable iff (1'b0)
        S[1] == (
            A[1] ^ B[1] ^
            (
                (A[0] & B[0]) |
                ((A[0] ^ B[0]) & Cin)
            )
        )
    );

    // Sum bit 2 must include carry propagation from bits 0 and 1.
    check_sum_bit2: assert property (
        @(posedge clk) disable iff (1'b0)
        S[2] == (
            A[2] ^ B[2] ^
            (
                (A[1] & B[1]) |
                (
                    (A[1] ^ B[1]) &
                    (
                        (A[0] & B[0]) |
                        ((A[0] ^ B[0]) & Cin)
                    )
                )
            )
        )
    );

    // Sum bit 3 must include carry propagation through the lower bits.
    check_sum_bit3: assert property (
        @(posedge clk) disable iff (1'b0)
        S[3] == (
            A[3] ^ B[3] ^
            (
                (A[2] & B[2]) |
                (
                    (A[2] ^ B[2]) &
                    (
                        (A[1] & B[1]) |
                        (
                            (A[1] ^ B[1]) &
                            (
                                (A[0] & B[0]) |
                                ((A[0] ^ B[0]) & Cin)
                            )
                        )
                    )
                )
            )
        )
    );

    // Carry-out must match the final ripple-carry equation.
    check_cout_logic: assert property (
        @(posedge clk) disable iff (1'b0)
        Cout == (
            (A[3] & B[3]) |
            (
                (A[3] ^ B[3]) &
                (
                    (A[2] & B[2]) |
                    (
                        (A[2] ^ B[2]) &
                        (
                            (A[1] & B[1]) |
                            (
                                (A[1] ^ B[1]) &
                                (
                                    (A[0] & B[0]) |
                                    ((A[0] ^ B[0]) & Cin)
                                )
                            )
                        )
                    )
                )
            )
        )
    );

    // Adding zero on B with no carry-in must pass A through unchanged.
    check_b_zero_identity: assert property (
        @(posedge clk) disable iff (1'b0)
        (B == 4'b0000 && Cin == 1'b0) |-> ({Cout, S} == {1'b0, A})
    );

    // Adding zero on A with no carry-in must pass B through unchanged.
    check_a_zero_identity: assert property (
        @(posedge clk) disable iff (1'b0)
        (A == 4'b0000 && Cin == 1'b0) |-> ({Cout, S} == {1'b0, B})
    );

endmodule