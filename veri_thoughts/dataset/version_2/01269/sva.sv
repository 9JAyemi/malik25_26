module comb_circuit_sva (
    input logic [2:0] A,
    input logic [2:0] B,
    input logic [2:0] C,
    input logic [2:0] Y1,
    input logic [2:0] Y2,
    input logic [2:0] Y3
);

    ///// Functional correctness /////
    // Y1 equals bitwise AND of A and B.
    check_y1_and: assert property (
        @($global_clock) Y1 == (A & B)
    );

    // Y2 equals bitwise OR of A and C.
    check_y2_or: assert property (
        @($global_clock) Y2 == (A | C)
    );

    // Y3 equals bitwise XOR of B and C.
    check_y3_xor: assert property (
        @($global_clock) Y3 == (B ^ C)
    );

    ///// Derived invariants from definitions /////
    // Y1 is a subset of A.
    check_y1_subset_a: assert property (
        @($global_clock) (Y1 & ~A) == 3'b000
    );

    // Y1 is a subset of B.
    check_y1_subset_b: assert property (
        @($global_clock) (Y1 & ~B) == 3'b000
    );

    // Y2 is a superset of A.
    check_y2_superset_a: assert property (
        @($global_clock) (A & ~Y2) == 3'b000
    );

    // Y2 is a superset of C.
    check_y2_superset_c: assert property (
        @($global_clock) (C & ~Y2) == 3'b000
    );

    // Inversion: B is Y3 XOR C.
    check_y3_invert_b: assert property (
        @($global_clock) (Y3 ^ C) == B
    );

    // Inversion: C is Y3 XOR B.
    check_y3_invert_c: assert property (
        @($global_clock) (Y3 ^ B) == C
    );

    // Y1 OR Y2 collapses to Y2.
    check_y1_or_y2_eq_y2: assert property (
        @($global_clock) (Y1 | Y2) == Y2
    );

    // Y1 AND Y2 collapses to Y1.
    check_y1_and_y2_eq_y1: assert property (
        @($global_clock) (Y1 & Y2) == Y1
    );

endmodule