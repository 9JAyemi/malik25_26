module four_bit_adder_sva (
    input logic CLK,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic CI,
    input logic [3:0] SUM,
    input logic CO
);
    // Combinational 4-bit adder; no reset in RTL; use CLK only for sampling.

    // SUM and CO together equal the 5-bit arithmetic sum of A+B+CI.
    check_sum_and_carry_are_arithmetic: assert property (
        @(posedge CLK) {CO, SUM} == ({1'b0, A} + {1'b0, B} + CI)
    );

    // CO equals the MSB of the 5-bit sum.
    check_carry_equals_sum_msb: assert property (
        @(posedge CLK) CO == ({1'b0, A} + {1'b0, B} + CI)[4]
    );

    // No carry-out when both MSBs are 0.
    check_no_carry_when_both_msb_zero: assert property (
        @(posedge CLK) (A[3] == 1'b0 && B[3] == 1'b0) |-> (CO == 1'b0)
    );

    // Carry-out must be 1 when both MSBs are 1.
    check_carry_when_both_msb_one: assert property (
        @(posedge CLK) (A[3] == 1'b1 && B[3] == 1'b1) |-> (CO == 1'b1)
    );

    // LSB sum bit is XOR of A[0], B[0], and CI.
    check_lsb_sum_xor: assert property (
        @(posedge CLK) SUM[0] == (A[0] ^ B[0] ^ CI)
    );

    // Adding B=0 with CI=0 yields SUM=A and CO=0.
    check_identity_b_zero_no_ci: assert property (
        @(posedge CLK) ((B == 4'b0000) && (CI == 1'b0)) |-> ((SUM == A) && (CO == 1'b0))
    );

    // Adding A=0 with CI=0 yields SUM=B and CO=0.
    check_identity_a_zero_no_ci: assert property (
        @(posedge CLK) ((A == 4'b0000) && (CI == 1'b0)) |-> ((SUM == B) && (CO == 1'b0))
    );

    // With A=0 and B=0, output equals CI (no carry-out).
    check_zero_plus_zero_ci_only: assert property (
        @(posedge CLK) ((A == 4'b0000) && (B == 4'b0000)) |-> ((CO == 1'b0) && (SUM == {3'b000, CI}))
    );

    // A + (~A) + 1 produces SUM=0 and CO=1.
    check_ones_complement_plus_one: assert property (
        @(posedge CLK) ((B == ~A) && (CI == 1'b1)) |-> ((SUM == 4'b0000) && (CO == 1'b1))
    );

    // When A==B and CI==0, result is A shifted left by 1 with carry=MSB of A.
    check_double_when_equal_no_ci: assert property (
        @(posedge CLK) ((A == B) && (CI == 1'b0)) |-> ({CO, SUM} == {A[3], {A[2:0], 1'b0}})
    );

    // Adding 0xF with CI=1 yields {1, A}.
    check_add_f_with_ci_one: assert property (
        @(posedge CLK) ((B == 4'hF) && (CI == 1'b1)) |-> ({CO, SUM} == {1'b1, A})
    );

    // A + (~A) with CI=0 produces SUM=0xF and CO=0.
    check_ones_complement_no_ci: assert property (
        @(posedge CLK) ((B == ~A) && (CI == 1'b0)) |-> ((SUM == 4'hF) && (CO == 1'b0))
    );
endmodule