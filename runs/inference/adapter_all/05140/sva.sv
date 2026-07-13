module four_bit_adder_sva (
    input logic [3:0] S,
    input logic       CO,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       CI
);
    // Combinational DUT with no clock/reset; sample on any input edge.

    // Sum and carry-out equal the 5-bit arithmetic result of A + B + CI.
    check_full_sum: assert property (
        @(posedge A[0] or negedge A[0] or
          posedge A[1] or negedge A[1] or
          posedge A[2] or negedge A[2] or
          posedge A[3] or negedge A[3] or
          posedge B[0] or negedge B[0] or
          posedge B[1] or negedge B[1] or
          posedge B[2] or negedge B[2] or
          posedge B[3] or negedge B[3] or
          posedge CI   or negedge CI)
        {CO, S} == ({1'b0, A} + {1'b0, B} + CI)
    );

    // Carry-out equals MSB of the 5-bit arithmetic result.
    check_carry_msb: assert property (
        @(posedge A[0] or negedge A[0] or
          posedge A[1] or negedge A[1] or
          posedge A[2] or negedge A[2] or
          posedge A[3] or negedge A[3] or
          posedge B[0] or negedge B[0] or
          posedge B[1] or negedge B[1] or
          posedge B[2] or negedge B[2] or
          posedge B[3] or negedge B[3] or
          posedge CI   or negedge CI)
        CO == (({1'b0, A} + {1'b0, B} + CI)[4])
    );

    // Sum equals lower 4 bits of the 5-bit arithmetic result.
    check_sum_lower_bits: assert property (
        @(posedge A[0] or negedge A[0] or
          posedge A[1] or negedge A[1] or
          posedge A[2] or negedge A[2] or
          posedge A[3] or negedge A[3] or
          posedge B[0] or negedge B[0] or
          posedge B[1] or negedge B[1] or
          posedge B[2] or negedge B[2] or
          posedge B[3] or negedge B[3] or
          posedge CI   or negedge CI)
        S == (({1'b0, A} + {1'b0, B} + CI)[3:0])
    );

    // Adding zero on B with CI=0 yields S=A and CO=0.
    check_add_zero_B: assert property (
        @(posedge A[0] or negedge A[0] or
          posedge A[1] or negedge A[1] or
          posedge A[2] or negedge A[2] or
          posedge A[3] or negedge A[3] or
          posedge B[0] or negedge B[0] or
          posedge B[1] or negedge B[1] or
          posedge B[2] or negedge B[2] or
          posedge B[3] or negedge B[3] or
          posedge CI   or negedge CI)
        (B == 4'b0000 && CI == 1'b0) |-> (S == A && CO == 1'b0)
    );

    // Adding zero on A with CI=0 yields S=B and CO=0.
    check_add_zero_A: assert property (
        @(posedge A[0] or negedge A[0] or
          posedge A[1] or negedge A[1] or
          posedge A[2] or negedge A[2] or
          posedge A[3] or negedge A[3] or
          posedge B[0] or negedge B[0] or
          posedge B[1] or negedge B[1] or
          posedge B[2] or negedge B[2] or
          posedge B[3] or negedge B[3] or
          posedge CI   or negedge CI)
        (A == 4'b0000 && CI == 1'b0) |-> (S == B && CO == 1'b0)
    );

    // With B=0 and CI=0, the result is A with no carry.
    check_identity_B_zero: assert property (
        @(posedge A[0] or negedge A[0] or
          posedge A[1] or negedge A[1] or
          posedge A[2] or negedge A[2] or
          posedge A[3] or negedge A[3] or
          posedge B[0] or negedge B[0] or
          posedge B[1] or negedge B[1] or
          posedge B[2] or negedge B[2] or
          posedge B[3] or negedge B[3] or
          posedge CI   or negedge CI)
        (B == 4'b0000 && CI == 1'b0) |-> (S == A && CO == 1'b0)
    );

    // With A=0 and CI=0, the result is B with no carry.
    check_identity_A_zero: assert property (
        @(posedge A[0] or negedge A[0] or
          posedge A[1] or negedge A[1] or
          posedge A[2] or negedge A[2] or
          posedge A[3] or negedge A[3] or
          posedge B[0] or negedge B[0] or
          posedge B[1] or negedge B[1] or
          posedge B[2] or negedge B[2] or
          posedge B[3] or negedge B[3] or
          posedge CI   or negedge CI)
        (A == 4'b0000 && CI == 1'b0) |-> (S == B && CO == 1'b0)
    );

    // With A=0 and B=0, the result is CI in bit 0 and no carry.
    check_zero_plus_zero: assert property (
        @(posedge A[0] or negedge A[0] or
          posedge A[1] or negedge A[1] or
          posedge A[2] or negedge A[2] or
          posedge A[3] or negedge A[3] or
          posedge B[0] or negedge B[0] or
          posedge B[1] or negedge B[1] or
          posedge B[2] or negedge B[2] or
          posedge B[3] or negedge B[3] or
          posedge CI   or negedge CI)
        (A == 4'b0000 && B == 4'b0000) |-> (S == {3'b000, CI} && CO == 1'b0)
    );

    // With A=0 and B=0 and CI=1, the result is 1 with no carry.
    check_zero_plus_zero_plus_one: assert property (
        @(posedge A[0] or negedge A[0] or
          posedge A[1] or negedge A[1] or
          posedge A[2] or negedge A[2] or
          posedge A[3] or negedge A[3] or
          posedge B[0] or negedge B[0] or
          posedge B[1] or negedge B[1] or
          posedge B[2] or negedge B[2] or
          posedge B[3] or negedge B[3] or
          posedge CI   or negedge CI)
        (A == 4'b0000 && B == 4'b0000 && CI == 1'b1) |-> (S == 4'b0001 && CO == 1'b0)
    );

    // With A=0 and B=0 and CI=0, the result is 0 with no carry.
    check_zero_plus_zero_plus_zero: assert property (
        @(posedge A[0] or negedge A[0] or
          posedge A[1] or negedge A[1] or
          posedge A[2] or negedge A[2] or
          posedge A[3] or negedge A[3] or
          posedge B[0] or negedge B[0] or
          posedge B[1] or negedge B[1] or
          posedge B[2] or negedge B[2] or
          posedge B[3]