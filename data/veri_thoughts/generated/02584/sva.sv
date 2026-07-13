module four_bit_adder_sva (
    input logic CLK,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Ci,
    input logic [3:0] S,
    input logic Co
);
    // 5-bit result matches arithmetic sum of inputs.
    check_sum_5bit: assert property (
        @(posedge CLK) disable iff (1'b0) {Co, S} == ({1'b0, A} + {1'b0, B} + Ci)
    );

    // LSB sum bit equals A0 ^ B0 ^ Ci.
    check_bit0_sum: assert property (
        @(posedge CLK) disable iff (1'b0) S[0] == (A[0] ^ B[0] ^ Ci)
    );

    // Bit1 sum equals A1 ^ B1 ^ C0.
    check_bit1_sum: assert property (
        @(posedge CLK) disable iff (1'b0)
            S[1] == (A[1] ^ B[1] ^ ((A[0] & B[0]) | ((A[0] ^ B[0]) & Ci)))
    );

    // Bit2 sum equals A2 ^ B2 ^ C1.
    check_bit2_sum: assert property (
        @(posedge CLK) disable iff (1'b0)
            S[2] == (A[2] ^ B[2] ^ (
                        (A[1] & B[1]) |
                        ((A[1] ^ B[1]) & ((A[0] & B[0]) | ((A[0] ^ B[0]) & Ci)))
                    ))
    );

    // Bit3 sum equals A3 ^ B3 ^ C2.
    check_bit3_sum: assert property (
        @(posedge CLK) disable iff (1'b0)
            S[3] == (A[3] ^ B[3] ^ (
                        (A[2] & B[2]) |
                        ((A[2] ^ B[2]) & (
                            (A[1] & B[1]) |
                            ((A[1] ^ B[1]) & ((A[0] & B[0]) | ((A[0] ^ B[0]) & Ci)))
                        ))
                    ))
    );

    // Final carry-out equals (A3 & B3) | ((A3 ^ B3) & C2).
    check_final_carry: assert property (
        @(posedge CLK) disable iff (1'b0)
            Co == (
                (A[3] & B[3]) |
                ((A[3] ^ B[3]) & (
                    (A[2] & B[2]) |
                    ((A[2] ^ B[2]) & (
                        (A[1] & B[1]) |
                        ((A[1] ^ B[1]) & ((A[0] & B[0]) | ((A[0] ^ B[0]) & Ci)))
                    ))
                ))
            )
    );

    // Outputs are stable across a cycle when inputs are stable.
    check_stability: assert property (
        @(posedge CLK) disable iff (1'b0)
            ($stable(A) && $stable(B) && $stable(Ci)) |-> ($stable(S) && $stable(Co))
    );

    // Adding zero B with zero carry-in passes A through, no carry-out.
    check_pass_through_A: assert property (
        @(posedge CLK) disable iff (1'b0)
            ((B == 4'b0000) && (Ci == 1'b0)) |-> ({Co, S} == {1'b0, A})
    );

    // Adding zero A with zero carry-in passes B through, no carry-out.
    check_pass_through_B: assert property (
        @(posedge CLK) disable iff (1'b0)
            ((A == 4'b0000) && (Ci == 1'b0)) |-> ({Co, S} == {1'b0, B})
    );

    // All zeros on inputs yield zero sum and zero carry.
    check_all_zero: assert property (
        @(posedge CLK) disable iff (1'b0)
            ((A == 4'b0000) && (B == 4'b0000) && (Ci == 1'b0)) |-> ((S == 4'b0000) && (Co == 1'b0))
    );

    // A + ~A + 1 = 16 => zero sum and carry-out set.
    check_complement_plus_one: assert property (
        @(posedge CLK) disable iff (1'b0)
            ((B == ~A) && (Ci == 1'b1)) |-> ((S == 4'b0000) && (Co == 1'b1))
    );
endmodule