module adder_4bit_sva (
    input logic CLK,
    input logic RESETn,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic CIN,
    input logic [3:0] S,
    input logic COUT
);
    // Outputs equal the 5-bit arithmetic sum of inputs.
    check_combined_sum_correct: assert property (
        @(posedge CLK) disable iff (!RESETn)
        {COUT, S} == ({1'b0, A} + {1'b0, B} + CIN)
    );

    // COUT is the MSB of the 5-bit sum.
    check_cout_is_msb_of_sum: assert property (
        @(posedge CLK) disable iff (!RESETn)
        COUT == (({1'b0, A} + {1'b0, B} + CIN)[4])
    );

    // LSB sum bit is XOR of input bits for a full-adder.
    check_s0_xor: assert property (
        @(posedge CLK) disable iff (!RESETn)
        S[0] == (A[0] ^ B[0] ^ CIN)
    );

    // No carry-out when total sum <= 15.
    check_no_carry_when_sum_le_15: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (({1'b0, A} + {1'b0, B} + CIN) <= 5'd15) |-> (COUT == 1'b0)
    );

    // Carry-out asserted when total sum >= 16.
    check_carry_when_sum_ge_16: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (({1'b0, A} + {1'b0, B} + CIN) >= 5'd16) |-> (COUT == 1'b1)
    );

    // Adding zero B with CIN=0 returns A, carry zero.
    check_add_zero_identity_b: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (B == 4'd0 && CIN == 1'b0) |-> ({COUT, S} == {1'b0, A})
    );

    // Adding zero A with CIN=0 returns B, carry zero.
    check_add_zero_identity_a: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (A == 4'd0 && CIN == 1'b0) |-> ({COUT, S} == {1'b0, B})
    );

    // With A=0 and B=0, sum equals CIN and carry is zero.
    check_zero_zero_cin_passthrough: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (A == 4'd0 && B == 4'd0) |-> (COUT == 1'b0 && S == {3'b000, CIN})
    );

    // With B bitwise complement of A and CIN=0, sum is 0xF and carry is zero.
    check_complement_no_carry_when_cin0: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (B == ~A && CIN == 1'b0) |-> (S == 4'hF && COUT == 1'b0)
    );

    // Corner case: 0xF + 0xF + 1 = 0xF with carry 1.
    check_max_plus_max_plus_one: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (A == 4'hF && B == 4'hF && CIN == 1'b1) |-> (S == 4'hF && COUT == 1'b1)
    );

    // If inputs are stable across a cycle, outputs remain stable.
    check_output_stable_when_inputs_stable: assert property (
        @(posedge CLK) disable iff (!RESETn)
        ($stable(A) && $stable(B) && $stable(CIN)) |-> $stable({COUT, S})
    );
endmodule