module three_to_one_sva (
    input logic CLK,
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [7:0] C,
    input logic [7:0] X
);
    ///// Functional equivalence /////
    // X must equal (A & B) ^ (B | C).
    check_function_equivalence_main: assert property (
        @(posedge CLK) X == ((A & B) ^ (B | C))
    );
    // X must also equal ((~A) & B) | (C & ~B).
    check_equivalence_mux_form: assert property (
        @(posedge CLK) X == (((~A) & B) | (C & ~B))
    );

    ///// Bit-level masking behaviors /////
    // Bits where B is 0: X must match C on those bits.
    check_bits_where_B_zero_match_C: assert property (
        @(posedge CLK) (((X ^ C) & ~B) == 8'h00)
    );
    // Bits where B is 1: X must match ~A on those bits.
    check_bits_where_B_one_match_notA: assert property (
        @(posedge CLK) (((X ^ (~A)) & B) == 8'h00)
    );

    ///// Special cases /////
    // If all bits of B are 0, X equals C.
    check_all_B_zero_implies_X_eq_C: assert property (
        @(posedge CLK) (B == 8'h00) |-> (X == C)
    );
    // If all bits of B are 1, X equals ~A.
    check_all_B_ones_implies_X_eq_notA: assert property (
        @(posedge CLK) (B == 8'hFF) |-> (X == (~A))
    );
    // If A equals C, X reduces to A ^ B.
    check_when_A_equals_C_then_X_eq_A_xor_B: assert property (
        @(posedge CLK) (A == C) |-> (X == (A ^ B))
    );
    // If C equals ~A, X equals ~A regardless of B.
    check_when_C_equals_notA_then_X_eq_notA: assert property (
        @(posedge CLK) (C == (~A)) |-> (X == (~A))
    );
    // If B equals C, X equals B & ~A.
    check_when_B_equals_C_then_X_eq_B_and_notA: assert property (
        @(posedge CLK) (B == C) |-> (X == (B & (~A)))
    );
    // If B equals ~C, X equals ~(A & B).
    check_when_B_equals_notC_then_X_eq_not_AandB: assert property (
        @(posedge CLK) (B == (~C)) |-> (X == (~(A & B)))
    );
endmodule