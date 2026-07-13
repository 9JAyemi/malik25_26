module alu_4bit_sva (
    input logic CLK,
    input logic [3:0] Z,
    input logic [1:0] op,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] C
);
    // For op=00, Z equals 4-bit A+B.
    check_add_correct: assert property (
        @(posedge CLK) (op == 2'b00) |-> (Z == (A + B))
    );

    // For op=00, Z-B equals A modulo 16.
    check_add_inverse: assert property (
        @(posedge CLK) (op == 2'b00) |-> ((Z - B) == A)
    );

    // For op=01, Z equals 4-bit A-B.
    check_sub_correct: assert property (
        @(posedge CLK) (op == 2'b01) |-> (Z == (A - B))
    );

    // For op=01, Z+B equals A modulo 16.
    check_sub_inverse: assert property (
        @(posedge CLK) (op == 2'b01) |-> ((Z + B) == A)
    );

    // For op=10, Z equals A & B.
    check_and_correct: assert property (
        @(posedge CLK) (op == 2'b10) |-> (Z == (A & B))
    );

    // For op=10, Z can only have bits set that are set in A.
    check_and_subset_A: assert property (
        @(posedge CLK) (op == 2'b10) |-> ((Z & ~A) == 4'b0000)
    );

    // For op=10, Z can only have bits set that are set in B.
    check_and_subset_B: assert property (
        @(posedge CLK) (op == 2'b10) |-> ((Z & ~B) == 4'b0000)
    );

    // For op=11, Z equals A | B.
    check_or_correct: assert property (
        @(posedge CLK) (op == 2'b11) |-> (Z == (A | B))
    );

    // For op=11, all bits set in A must be set in Z.
    check_or_superset_A: assert property (
        @(posedge CLK) (op == 2'b11) |-> ((~Z & A) == 4'b0000)
    );

    // For op=11, all bits set in B must be set in Z.
    check_or_superset_B: assert property (
        @(posedge CLK) (op == 2'b11) |-> ((~Z & B) == 4'b0000)
    );

    // If op, A, and B are stable, Z must remain stable.
    check_stable_when_inputs_stable: assert property (
        @(posedge CLK) $stable({op,A,B}) |-> $stable(Z)
    );

    // Z must be independent of C; C changes alone cannot change Z.
    check_independent_of_C: assert property (
        @(posedge CLK) $stable({op,A,B}) && $changed(C) |-> $stable(Z)
    );
endmodule