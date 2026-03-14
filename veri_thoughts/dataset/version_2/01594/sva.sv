module Adder_sva (
    input logic [7:0]  A,
    input logic [7:0]  B,
    input logic [15:0] C
);
    // No clock/reset in RTL; sample assertions on posedge of A[0].
    // Output equals zero-extended sum of A and B.
    check_sum_function: assert property (
        @(posedge A[0]) C == ({8'b0, A} + {8'b0, B})
    );

    // Upper seven bits are always zero.
    check_upper_seven_zero: assert property (
        @(posedge A[0]) C[15:9] == 7'b0
    );

    // Carry-out bit matches bit[8] of zero-extended sum.
    check_carry_bit: assert property (
        @(posedge A[0]) C[8] == (({8'b0, A} + {8'b0, B})[8])
    );

    // Low 8 bits equal the low 8 bits of the zero-extended sum.
    check_low_byte: assert property (
        @(posedge A[0]) C[7:0] == (({8'b0, A} + {8'b0, B})[7:0])
    );

    // Commutativity holds for the implemented expression.
    check_commutative: assert property (
        @(posedge A[0]) C == ({8'b0, B} + {8'b0, A})
    );

    // Sum is at least A.
    check_ge_A: assert property (
        @(posedge A[0]) C >= {8'b0, A}
    );

    // Sum is at least B.
    check_ge_B: assert property (
        @(posedge A[0]) C >= {8'b0, B}
    );

    // Sum never exceeds 510 (max 255+255).
    check_upper_bound: assert property (
        @(posedge A[0]) C <= 16'd510
    );

    // If B is zero, C equals A zero-extended.
    check_B_zero_identity: assert property (
        @(posedge A[0]) (B == 8'b0) |-> (C == {8'b0, A})
    );

    // If A is zero, C equals B zero-extended.
    check_A_zero_identity: assert property (
        @(posedge A[0]) (A == 8'b0) |-> (C == {8'b0, B})
    );
endmodule