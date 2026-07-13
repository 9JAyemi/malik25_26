module four_bit_adder_sva (
    input logic CLK,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    input logic [3:0] S,
    input logic Cout
);
    // Outputs equal full 5-bit sum of inputs.
    check_sum_full: assert property (
        @(posedge CLK) {Cout, S} == (A + B + Cin)
    );

    // Lower 4 bits of sum match S.
    check_sum_lower_bits: assert property (
        @(posedge CLK) S == (A + B + Cin)[3:0]
    );

    // Carry-out is the overflow of 4-bit addition.
    check_cout_overflow_flag: assert property (
        @(posedge CLK) Cout == ((A + B + Cin) > 4'hF)
    );

    // LSB sum bit is XOR of inputs.
    check_s0_xor: assert property (
        @(posedge CLK) S[0] == (A[0] ^ B[0] ^ Cin)
    );

    // S[1] uses carry from bit0.
    check_s1_with_c1: assert property (
        @(posedge CLK) S[1] == (A[1] ^ B[1] ^ ((A[0] & B[0]) | ((A[0] ^ B[0]) & Cin)))
    );

    // S[2] uses carry from bit1 which depends on bit0.
    check_s2_with_c2: assert property (
        @(posedge CLK) S[2] == (A[2] ^ B[2] ^ (
            (A[1] & B[1]) | ((A[1] ^ B[1]) & ((A[0] & B[0]) | ((A[0] ^ B[0]) & Cin)))
        ))
    );

    // S[3] uses carry from bit2 which depends on lower bits.
    check_s3_with_c3: assert property (
        @(posedge CLK) S[3] == (A[3] ^ B[3] ^ (
            (A[2] & B[2]) | ((A[2] ^ B[2]) & (
                (A[1] & B[1]) | ((A[1] ^ B[1]) & ((A[0] & B[0]) | ((A[0] ^ B[0]) & Cin)))
            ))
        ))
    );

    // Cout equals carry out of bit3 from full carry chain.
    check_cout_from_c4: assert property (
        @(posedge CLK) Cout == (
            (A[3] & B[3]) | ((A[3] ^ B[3]) & (
                (A[2] & B[2]) | ((A[2] ^ B[2]) & (
                    (A[1] & B[1]) | ((A[1] ^ B[1]) & (
                        (A[0] & B[0]) | ((A[0] ^ B[0]) & Cin)
                    ))
                ))
            ))
        )
    );

    // If inputs do not change between cycles, outputs do not change.
    check_stability_when_inputs_stable: assert property (
        @(posedge CLK) ((A == $past(A)) && (B == $past(B)) && (Cin == $past(Cin)))
        |-> ((S == $past(S)) && (Cout == $past(Cout)))
    );

    // Zero inputs produce zero sum and no carry.
    check_zero_case: assert property (
        @(posedge CLK) ((A == 4'b0000) && (B == 4'b0000) && (Cin == 1'b0))
        |-> ((S == 4'b0000) && (Cout == 1'b0))
    );

    // Max inputs with Cin=1 saturate S and set Cout.
    check_max_case: assert property (
        @(posedge CLK) ((A == 4'hF) && (B == 4'hF) && (Cin == 1'b1))
        |-> ((S == 4'hF) && (Cout == 1'b1))
    );

    // With Cin=0, outputs equal A+B.
    check_cin_zero_sum: assert property (
        @(posedge CLK) (Cin == 1'b0) |-> ({Cout, S} == (A + B))
    );

    // With Cin=1, outputs equal A+B+1.
    check_cin_one_sum: assert property (
        @(posedge CLK) (Cin == 1'b1) |-> ({Cout, S} == (A + B + 1'b1))
    );
endmodule