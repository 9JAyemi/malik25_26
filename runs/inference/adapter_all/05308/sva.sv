module four_bit_adder_sva (
    input logic CLK,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] sum
);
    // Sum equals A + B (4-bit wraparound).
    check_sum_matches_add: assert property (
        @(posedge CLK) sum == (A + B)
    );

    // LSB sum is XOR of A[0] and B[0] (cin=0).
    check_sum_bit0_xor: assert property (
        @(posedge CLK) sum[0] == (A[0] ^ B[0])
    );

    // Bit1 sum equals XOR of A[1], B[0], and carry from bit0.
    check_sum_bit1_with_carry0: assert property (
        @(posedge CLK) sum[1] == (A[1] ^ B[0] ^ (A[0] & B[0]))
    );

    // Bit2 sum equals XOR of A[2], B[1], and carry from bit1.
    check_sum_bit2_with_carry1: assert property (
        @(posedge CLK) sum[2] == (A[2] ^ B[1] ^ ((A[1] & B[0]) | (A[0] & B[0])))
    );

    // Bit3 sum equals XOR of A[3], B[2], and carry from bit2.
    check_sum_bit3_with_carry2: assert property (
        @(posedge CLK) sum[3] == (A[3] ^ B[2] ^ ((A[2] & B[1]) | (A[1] & B[0]) | (A[0] & B[0])))
    );

    // Carry-out equals carry from bit3.
    check_carry_out_from_bit3: assert property (
        @(posedge CLK) sum[3] == (A[3] ^ B[2] ^ ((A[2] & B[1]) | (A[1] & B[0]) | (A[0] & B[0])))
    );

    // If inputs are stable, sum remains stable.
    check_stability_when_inputs_stable: assert property (
        @(posedge CLK) $stable(A) && $stable(B) |-> $stable(sum)
    );

    // If sum changes, at least one input must have changed.
    check_sum_change_implies_input_change: assert property (
        @(posedge CLK) $changed(sum) |-> ($changed(A) || $changed(B))
    );

    // Adding zero on B passes A through.
    check_add_zero_B: assert property (
        @(posedge CLK) (B == 4'h0) |-> (sum == A)
    );

    // Adding zero on A passes B through.
    check_add_zero_A: assert property (
        @(posedge CLK) (A == 4'h0) |-> (sum == B)
    );

    // If A and B are equal, sum is zero.
    check_equal_inputs_zero_sum: assert property (
        @(posedge CLK) (A == B) |-> (sum == 4'h0)
    );
endmodule