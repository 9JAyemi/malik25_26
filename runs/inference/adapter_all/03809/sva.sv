module adder_subtractor_4bit_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic SUB,
    input logic [3:0] result,
    input logic OVFL
);
    // In add mode, result equals A + B (4-bit wrap).
    check_add_mode_result: assert property (
        @(posedge SUB or negedge SUB or posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3] or posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1] or posedge B[2] or negedge B[2] or posedge B[3] or negedge B[3])
        (SUB == 1'b0) |-> (result == (A + B))
    );

    // In subtract mode, result equals A - B (4-bit wrap).
    check_sub_mode_result: assert property (
        @(posedge SUB or negedge SUB or posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3] or posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1] or posedge B[2] or negedge B[2] or posedge B[3] or negedge B[3])
        (SUB == 1'b1) |-> (result == (A - B))
    );

    // In add mode, OVFL reflects sign bit of A + B.
    check_add_mode_ovfl: assert property (
        @(posedge SUB or negedge SUB or posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3] or posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1] or posedge B[2] or negedge B[2] or posedge B[3] or negedge B[3])
        (SUB == 1'b0) |-> (OVFL == ((A + B)[3]))
    );

    // In subtract mode, OVFL reflects sign bit of A - B.
    check_sub_mode_ovfl: assert property (
        @(posedge SUB or negedge SUB or posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3] or posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1] or posedge B[2] or negedge B[2] or posedge B[3] or negedge B[3])
        (SUB == 1'b1) |-> (OVFL == ((A - B)[3]))
    );

    // In add mode, if A == 0 then result == B.
    check_add_zero_a: assert property (
        @(posedge SUB or negedge SUB or posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3] or posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1] or posedge B[2] or negedge B[2] or posedge B[3] or negedge B[3])
        (SUB == 1'b0 && A == 4'b0000) |-> (result == B)
    );

    // In add mode, if B == 0 then result == A.
    check_add_zero_b: assert property (
        @(posedge SUB or negedge SUB or posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3] or posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1] or posedge B[2] or negedge B[2] or posedge B[3] or negedge B[3])
        (SUB == 1'b0 && B == 4'b0000) |-> (result == A)
    );

    // In subtract mode, if B == 0 then result == A.
    check_sub_zero_b: assert property (
        @(posedge SUB or negedge SUB or posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3] or posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1] or posedge B[2] or negedge B[2] or posedge B[3] or negedge B[3])
        (SUB == 1'b1 && B == 4'b0000) |-> (result == A)
    );

    // In subtract mode, if A == B then result == 0.
    check_sub_equal_operands_zero: assert property (
        @(posedge SUB or negedge SUB or posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3] or posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1] or posedge B[2] or negedge B[2] or posedge B[3] or negedge B[3])
        (SUB == 1'b1 && A == B) |-> (result == 4'b0000)
    );

    // In add mode, if A == ~B then result == 0 (4-bit wrap).
    check_add_complement_zero: assert property (
        @(posedge SUB or negedge SUB or posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3] or posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1] or posedge B[2] or negedge B[2] or posedge B[3] or negedge B[3])
        (SUB == 1'b0 && A == ~B) |-> (result == 4'b0000)
    );

    // In subtract mode, if A == ~B then result == 0 (4-bit wrap).
    check_sub_complement_zero: assert property (
        @(posedge SUB or negedge SUB or posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3] or posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1] or posedge B[2] or negedge B[2] or posedge B[3] or negedge B[3])
        (SUB == 1'b1 && A == ~B) |-> (result == 4'b0000)
    );

    // In add mode, if B == ~A then result == 0 (4-bit wrap).
    check_add_b_is_complement_of_a: assert property (
        @(posedge SUB or negedge SUB or posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3] or posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1] or posedge B[2] or negedge B[2] or posedge B[3] or negedge B[3])
        (SUB == 1'b0 && B == ~A) |-> (result == 4'b0000)
    );

    // In subtract mode, if B == ~A then result == 0 (4-bit wrap).
    check_sub_b_is_complement_of_a: assert property (
        @(posedge SUB or negedge SUB or posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or posedge A