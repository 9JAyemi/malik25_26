module four_bit_adder_sva (
    input logic CLK,          // sampling clock for SVA
    input logic [3:0] A,
    input logic [3:0] B,
    input logic CI,
    input logic CO,
    input logic [3:0] S
);
    // Sum and carry-out equal the 5-bit addition of inputs.
    sum_matches_addition: assert property (
        @(posedge CLK) {CO, S} == ({1'b0, A} + {1'b0, B} + CI)
    );

    // S equals lower 4 bits of the 5-bit sum.
    s_is_lower_nibble_of_sum: assert property (
        @(posedge CLK) S == (({1'b0, A} + {1'b0, B} + CI)[3:0])
    );

    // CO equals MSB of the 5-bit sum.
    co_is_msb_of_sum: assert property (
        @(posedge CLK) CO == (({1'b0, A} + {1'b0, B} + CI)[4])
    );

    // LSB sum equals XOR of inputs.
    lsb_xor_rule: assert property (
        @(posedge CLK) S[0] == (A[0] ^ B[0] ^ CI)
    );

    // Identity: when B==0 and CI==0, output equals A with no carry.
    identity_b_zero_ci_zero: assert property (
        @(posedge CLK) (B == 4'b0000) && (CI == 1'b0) |-> (S == A) && (CO == 1'b0)
    );

    // Identity: when A==0 and CI==0, output equals B with no carry.
    identity_a_zero_ci_zero: assert property (
        @(posedge CLK) (A == 4'b0000) && (CI == 1'b0) |-> (S == B) && (CO == 1'b0)
    );

    // Corner case: when A==0 and B==0, S echoes CI and CO is 0.
    zero_inputs_corner: assert property (
        @(posedge CLK) (A == 4'b0000) && (B == 4'b0000) |-> (S == {3'b000, CI}) && (CO == 1'b0)
    );

    // No carry-out when 5-bit sum is less than 16.
    no_carry_without_overflow: assert property (
        @(posedge CLK) (({1'b0, A} + {1'b0, B} + CI) < 5'd16) |-> (CO == 1'b0)
    );

    // Carry-out asserted when 5-bit sum is 16 or more.
    carry_with_overflow: assert property (
        @(posedge CLK) (({1'b0, A} + {1'b0, B} + CI) >= 5'd16) |-> (CO == 1'b1)
    );

    // Outputs remain stable when inputs are stable between samples.
    outputs_stable_when_inputs_stable: assert property (
        @(posedge CLK) $stable(A) && $stable(B) && $stable(CI) |-> $stable(S) && $stable(CO)
    );
endmodule