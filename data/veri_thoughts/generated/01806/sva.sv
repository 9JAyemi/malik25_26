module four_bit_adder_structural_sva (
    input logic CLK,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] S
);
    // S equals the lower 4 bits of A+B (ripple-carry with cin=0).
    check_sum_mod16: assert property (
        @(posedge CLK) S == (A + B)[3:0]
    );

    // LSB sum equals XOR of A[0] and B[0] (cin=0).
    check_bit0_xor: assert property (
        @(posedge CLK) S[0] == (A[0] ^ B[0])
    );

    // Bit1 sum equals XOR of A[1], B[1], and carry from bit0.
    check_bit1_ripple: assert property (
        @(posedge CLK) S[1] == (A[1] ^ B[1] ^ (A[0] & B[0]))
    );

    // Bit2 sum equals XOR of A[2], B[2], and carry from bit1.
    check_bit2_ripple: assert property (
        @(posedge CLK) S[2] == (A[2] ^ B[2] ^ ((A[1] & B[1]) | (A[1] & (A[0] & B[0])) | (B[1] & (A[0] & B[0]))))
    );

    // Bit3 sum equals XOR of A[3], B[3], and carry from bit2.
    check_bit3_ripple: assert property (
        @(posedge CLK) S[3] == (A[3] ^ B[3] ^ (
            (A[2] & B[2]) |
            (A[2] & ((A[1] & B[1]) | (A[1] & (A[0] & B[0])) | (B[1] & (A[0] & B[0])))) |
            (B[2] & ((A[1] & B[1]) | (A[1] & (A[0] & B[0])) | (B[1] & (A[0] & B[0]))))
        ))
    );

    // If A is zero, S must equal B.
    check_add_zero_A: assert property (
        @(posedge CLK) (A == 4'b0000) |-> (S == B)
    );

    // If B is zero, S must equal A.
    check_add_zero_B: assert property (
        @(posedge CLK) (B == 4'b0000) |-> (S == A)
    );

    // If B is the bitwise complement of A, S must be 0xF (mod-16 sum).
    check_complement_sums_to_all_ones: assert property (
        @(posedge CLK) (B == ~A) |-> (S == 4'hF)
    );

    // If inputs are stable across a cycle, the output is stable.
    check_stable_inputs_hold_output: assert property (
        @(posedge CLK) ($stable(A) && $stable(B)) |-> $stable(S)
    );

    // Output can only change if at least one input changes.
    check_output_change_implies_input_change: assert property (
        @(posedge CLK) $changed(S) |-> ($changed(A) || $changed(B))
    );
endmodule