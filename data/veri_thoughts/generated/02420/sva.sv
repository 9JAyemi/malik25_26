module binary_adder_sva (
    input logic CLK,
    input logic [1:0] A,
    input logic [1:0] B,
    input logic [1:0] SUM
);
    // Clock: CLK (posedge). No reset in RTL.
    // Logic: Mixed — combinational XOR/AND feeding registered outputs via DFFs.
    // Behavior: SUM[i] is the XOR of A[i] and B[i] sampled on the prior rising CLK.

    ///// Core functional relation /////
    // SUM equals the previous cycle's bitwise XOR of A and B.
    check_sum_matches_prev_xor_vector: assert property (
        @(posedge CLK) $past(1'b1) |-> (SUM == $past(A ^ B))
    );

    ///// Temporal consistency /////
    // If the previous XOR value changed from two cycles ago to one cycle ago, SUM must change from last cycle to this cycle.
    check_sum_changes_when_prev_xor_changes: assert property (
        @(posedge CLK) $past(1'b1,2) && ($past(A ^ B,1) != $past(A ^ B,2)) |-> (SUM != $past(SUM))
    );
    // If the previous XOR value stayed the same across the last two cycles, SUM must also stay the same.
    check_sum_stable_when_prev_xor_stable: assert property (
        @(posedge CLK) $past(1'b1,2) && ($past(A ^ B,1) == $past(A ^ B,2)) |-> (SUM == $past(SUM))
    );

    ///// Bit-accurate implications /////
    // For bit 0: if prior A[0]==B[0], then SUM[0]==0.
    check_bit0_prev_equal_implies_zero: assert property (
        @(posedge CLK) $past(1'b1) && ($past(A[0]) == $past(B[0])) |-> (SUM[0] == 1'b0)
    );
    // For bit 0: if prior A[0]!=B[0], then SUM[0]==1.
    check_bit0_prev_diff_implies_one: assert property (
        @(posedge CLK) $past(1'b1) && ($past(A[0]) != $past(B[0])) |-> (SUM[0] == 1'b1)
    );
    // For bit 1: if prior A[1]==B[1], then SUM[1]==0.
    check_bit1_prev_equal_implies_zero: assert property (
        @(posedge CLK) $past(1'b1) && ($past(A[1]) == $past(B[1])) |-> (SUM[1] == 1'b0)
    );
    // For bit 1: if prior A[1]!=B[1], then SUM[1]==1.
    check_bit1_prev_diff_implies_one: assert property (
        @(posedge CLK) $past(1'b1) && ($past(A[1]) != $past(B[1])) |-> (SUM[1] == 1'b1)
    );

    ///// Bitwise independence sanity /////
    // If the prior XOR bits differ from each other, the corresponding SUM bits must differ.
    check_per_bit_independence: assert property (
        @(posedge CLK) $past(1'b1) && ($past(A[0] ^ B[0]) != $past(A[1] ^ B[1])) |-> (SUM[0] != SUM[1])
    );

endmodule