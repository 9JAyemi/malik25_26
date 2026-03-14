module binary_adder_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] S,
    input logic       C_out
);
    // Combinational DUT; no clock/reset in RTL. Use $global_clock for SVA sampling.

    // Sum and carry-out must equal 5-bit addition of A and B (C_in = 0).
    check_sum_matches_addition: assert property (
        @(posedge $global_clock) {C_out, S} == ({1'b0, A} + {1'b0, B})
    );

    // Bit0 sum equals A[0] XOR B[0] (no carry-in).
    check_sum0_no_cin: assert property (
        @(posedge $global_clock) S[0] == (A[0] ^ B[0])
    );

    // Bit1 sum equals A[1] XOR B[1] XOR carry from bit0.
    check_sum1_ripple_logic: assert property (
        @(posedge $global_clock) S[1] == (A[1] ^ B[1] ^ (A[0] & B[0]))
    );

    // Bit2 sum equals A[2] XOR B[2] XOR carry from bit1.
    check_sum2_ripple_logic: assert property (
        @(posedge $global_clock) S[2] == (
            A[2] ^ B[2] ^ ( (A[1] & B[1]) | ((A[1] ^ B[1]) & (A[0] & B[0])) )
        )
    );

    // Carry-out equals ripple-carry equation from inputs A and B.
    check_cout_ripple_logic: assert property (
        @(posedge $global_clock) C_out == (
            (A[3] & B[3]) |
            ((A[3] ^ B[3]) & (
                (A[2] & B[2]) |
                ((A[2] ^ B[2]) & (
                    (A[1] & B[1]) |
                    ((A[1] ^ B[1]) & (A[0] & B[0]))
                ))
            ))
        )
    );

    // When A == 0, output passes B with no carry-out.
    check_passthrough_when_A_zero: assert property (
        @(posedge $global_clock) (A == 4'b0000) |-> (S == B) && (C_out == 1'b0)
    );

    // When B == 0, output passes A with no carry-out.
    check_passthrough_when_B_zero: assert property (
        @(posedge $global_clock) (B == 4'b0000) |-> (S == A) && (C_out == 1'b0)
    );

    // If both MSBs are 0, no carry-out can occur.
    check_cout_zero_when_MSBs_zero: assert property (
        @(posedge $global_clock) ((A[3] == 1'b0) && (B[3] == 1'b0)) |-> (C_out == 1'b0)
    );

    // If both MSBs are 1, carry-out must occur.
    check_cout_one_when_MSBs_one: assert property (
        @(posedge $global_clock) ((A[3] == 1'b1) && (B[3] == 1'b1)) |-> (C_out == 1'b1)
    );

    // Outputs remain stable when inputs remain stable (purely combinational).
    check_outputs_stable_when_inputs_stable: assert property (
        @(posedge $global_clock) ($stable(A) && $stable(B)) |-> $stable({S, C_out})
    );
endmodule