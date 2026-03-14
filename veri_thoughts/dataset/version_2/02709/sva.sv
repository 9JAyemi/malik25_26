module adder_4bit_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] S,
    input logic C_out
);
    ///// Functional equivalence to addition /////
    // The 5-bit result equals zero-extended A + B.
    check_sum_matches_addition: assert property (
        @(posedge clk) {C_out, S} == ({1'b0, A} + {1'b0, B})
    );

    ///// Bit 0 (no carry-in) /////
    // LSB sum equals A0 XOR B0.
    check_s0_no_cin: assert property (
        @(posedge clk) S[0] == (A[0] ^ B[0])
    );

    ///// Bit 1 with carry from bit 0 /////
    // Bit1 sum equals A1 XOR B1 XOR (A0 & B0).
    check_s1_with_c0: assert property (
        @(posedge clk) S[1] == (A[1] ^ B[1] ^ (A[0] & B[0]))
    );
    // If no carry from bit0, S1 is A1 XOR B1.
    check_s1_when_c0_zero: assert property (
        @(posedge clk) (~(A[0] & B[0])) |-> (S[1] == (A[1] ^ B[1]))
    );
    // If carry from bit0, S1 is inverted XOR of A1 and B1.
    check_s1_when_c0_one: assert property (
        @(posedge clk) (A[0] & B[0]) |-> (S[1] == ~(A[1] ^ B[1]))
    );

    ///// Bit 2 with ripple carry /////
    // Bit2 sum equals A2 XOR B2 XOR C1 (expanded C1).
    check_s2_with_c1: assert property (
        @(posedge clk) S[2] == (A[2] ^ B[2] ^ ((A[1] & B[1]) | ((A[1] ^ B[1]) & (A[0] & B[0]))))
    );
    // If C0==0 and A1==B1, then C1==A1&B1 so S2==A2 XOR B2 XOR (A1&B1).
    check_s2_c1_reduction: assert property (
        @(posedge clk) (~(A[0] & B[0]) && (A[1] == B[1])) |-> (S[2] == (A[2] ^ B[2] ^ (A[1] & B[1])))
    );
    // If C0==1 and (A1^B1)==1, then C1==1 so S2==~(A2^B2).
    check_s2_when_carry_generate: assert property (
        @(posedge clk) ((A[0] & B[0]) && (A[1] ^ B[1])) |-> (S[2] == ~(A[2] ^ B[2]))
    );

    ///// Bit 3 with ripple carry /////
    // Bit3 sum equals A3 XOR B3 XOR C2 (expanded C2).
    check_s3_with_c2: assert property (
        @(posedge clk) S[3] == (A[3] ^ B[3] ^ ((A[2] & B[2]) | ((A[2] ^ B[2]) & ((A[1] & B[1]) | ((A[1] ^ B[1]) & (A[0] & B[0]))))))
    );

    ///// Final carry-out /////
    // C_out equals C3 (expanded from ripple logic).
    check_cout_with_c3: assert property (
        @(posedge clk) C_out == ((A[3] & B[3]) | ((A[3] ^ B[3]) & ((A[2] & B[2]) | ((A[2] ^ B[2]) & ((A[1] & B[1]) | ((A[1] ^ B[1]) & (A[0] & B[0])))))))
    );
    // If MSB inputs are both 1, C_out must be 1.
    check_cout_when_msb_both_one: assert property (
        @(posedge clk) (A[3] & B[3]) |-> (C_out == 1'b1)
    );
    // If MSB inputs are both 0, C_out must be 0.
    check_cout_when_msb_both_zero: assert property (
        @(posedge clk) (~A[3] & ~B[3]) |-> (C_out == 1'b0)
    );

    ///// Sanity and stability /////
    // Adding 0 + 0 yields 0 with no carry.
    check_zero_plus_zero: assert property (
        @(posedge clk) ((A == 4'b0000) && (B == 4'b0000)) |-> ((S == 4'b0000) && (C_out == 1'b0))
    );
    // Adding 15 + 15 yields 30 => S=14 and C_out=1.
    check_max_plus_max: assert property (
        @(posedge clk) ((A == 4'b1111) && (B == 4'b1111)) |-> ((S == 4'b1110) && (C_out == 1'b1))
    );
    // If inputs are stable cycle-to-cycle, outputs are stable (pure combinational).
    check_outputs_stable_when_inputs_stable: assert property (
        @(posedge clk) ($stable(A) && $stable(B)) |-> ($stable(S) && $stable(C_out))
    );

endmodule