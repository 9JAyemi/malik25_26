module logic_function_sva (
    input logic CLK,
    input logic A,
    input logic B,
    input logic Ci,
    input logic S,
    input logic Co
);
    // S equals ~(Ci ^ ~(A ^ B)) as coded.
    check_sum_xnor_chain: assert property (
        @(posedge CLK) S == ~(Ci ^ ~(A ^ B))
    );

    // S equals three-input XOR of A, B, and Ci.
    check_sum_triple_xor: assert property (
        @(posedge CLK) S == (A ^ B ^ Ci)
    );

    // When A and B are equal, S mirrors Ci.
    check_sum_when_AeqB: assert property (
        @(posedge CLK) (A == B) |-> (S == Ci)
    );

    // When A and B differ, S is the inverse of Ci.
    check_sum_when_AneB: assert property (
        @(posedge CLK) (A != B) |-> (S == ~Ci)
    );

    // S ^ Ci equals A ^ B (rearranged XOR identity).
    check_sum_xor_relation: assert property (
        @(posedge CLK) (S ^ Ci) == (A ^ B)
    );

    // Co equals ~( (A & B & Ci) & ~(A & B) ) as coded.
    check_carry_expr: assert property (
        @(posedge CLK) Co == ~((A & B & Ci) & ~(A & B))
    );

    // Co is constant HIGH for all input combinations (logic simplification).
    check_carry_const_high: assert property (
        @(posedge CLK) Co == 1'b1
    );
endmodule