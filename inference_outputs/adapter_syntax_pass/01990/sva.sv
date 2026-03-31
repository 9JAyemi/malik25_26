module FullAdder_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic Ci,
    input logic S,
    input logic Co
);
    // Sum equals A ^ B ^ Ci.
    check_sum_xor: assert property (
        @(posedge clk) S == (A ^ B ^ Ci)
    );

    // Carry-out equals (A & B) | ((A ^ B) & Ci).
    check_carry_or_and: assert property (
        @(posedge clk) Co == ((A & B) | ((A ^ B) & Ci))
    );

    // When Ci is 0, sum equals A ^ B.
    check_sum_when_cin0: assert property (
        @(posedge clk) (Ci == 1'b0) |-> (S == (A ^ B))
    );

    // When Ci is 1, sum equals ~(A ^ B).
    check_sum_when_cin1: assert property (
        @(posedge clk) (Ci == 1'b1) |-> (S == ~(A ^ B))
    );

    // When Ci is 0, carry-out equals A & B.
    check_carry_when_cin0: assert property (
        @(posedge clk) (Ci == 1'b0) |-> (Co == (A & B))
    );

    // When Ci is 1, carry-out equals A | B.
    check_carry_when_cin1: assert property (
        @(posedge clk) (Ci == 1'b1) |-> (Co == (A | B))
    );

    // When A and B are equal, sum equals Ci.
    check_sum_when_ab_equal: assert property (
        @(posedge clk) (A == B) |-> (S == Ci)
    );

    // When A and B are equal, carry-out equals Ci.
    check_carry_when_ab_equal: assert property (
        @(posedge clk) (A == B) |-> (Co == Ci)
    );

    // When A and B differ, sum equals ~Ci.
    check_sum_when_ab_diff: assert property (
        @(posedge clk) (A != B) |-> (S == ~Ci)
    );

    // When A and B differ, carry-out equals Ci.
    check_carry_when_ab_diff: assert property (
        @(posedge clk) (A != B) |-> (Co == Ci)
    );
endmodule

module Mux1_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic Sel,
    input logic Out
);
    // Out equals selected input.
    check_mux_function: assert property (
        @(posedge clk) Out == (Sel ? A : B)
    );

    // When Sel is 0, Out equals B.
    check_out_when_sel0: assert property (
        @(posedge clk) (Sel == 1'b0) |-> (Out == B)
    );

    // When Sel is 1, Out equals A.
    check_out_when_sel1: assert property (
        @(posedge clk) (Sel == 1'b1) |-> (Out == A)
    );
endmodule

module Mux4bit_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Sel,
    input logic [3:0] Out
);
    // Out equals selected input vector.
    check_mux4_function: assert property (
        @(posedge clk) Out == (Sel ? A : B)
    );

    // When Sel is 0, Out equals B.
    check_out4_when_sel0: assert property (
        @(posedge clk) (Sel == 1'b0) |-> (Out == B)
    );

    // When Sel is 1, Out equals A.
    check_out4_when_sel1: assert property (
        @(posedge clk) (Sel == 1'b1) |-> (Out == A)
    );
endmodule

module RippleCarryAdder4bit_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Ci,
    input logic [3:0] S,
    input logic Co
);
    // Sum vector equals A + B + Ci.
    check_sum_vector_add: assert property (
        @(posedge clk) S == (A + B + Ci)
    );

    // Carry-out equals carry from the MSB stage.
    check_carry_out: assert property (
        @(posedge clk) Co == ((A[3] & B[3]) | ((A[3] ^ B[3]) & Ci))
    );

    // When Ci is 0, sum equals A + B.
    check_sum_when_cin0: assert property (
        @(posedge clk) (Ci == 1'b0) |-> (S == (A + B))
    );

    // When Ci is 1, sum equals A + B + 1.
    check_sum_when_cin1: assert property (
        @(posedge clk) (Ci == 1'b1) |-> (S == (A + B + 1'b1))
    );

    // When Ci is 0, carry-out equals A[3] & B[3].
    check_carry_when_cin0: assert property (
        @(posedge clk) (Ci == 1'b0) |-> (Co == (A[3] & B[3]))
    );

    // When Ci is 1, carry-out equals A[3] | B[3].
    check_carry_when_cin1: assert property (
        @(posedge clk) (Ci == 1'b1) |-> (Co == (A[3] | B[3]))
    );

    // When A and B are zero, sum equals Ci.
    check_sum_when_ab_zero: assert property (
        @(posedge clk) ((A == 4'b0000) && (B == 4'b0000)) |-> (S == Ci)
    );

    // When A and B are all ones, sum equals ~Ci.
    check_sum_when_ab_allones: assert property (
        @(posedge clk) ((A == 4'b1111) && (B == 4'b1111)) |-> (S == ~Ci)
    );

    // When A is zero and B is all ones, sum equals ~Ci.
    check_sum_when_a_zero_b_allones: assert property (
        @(posedge clk) ((A == 4'b0000) && (B == 4'b1111)) |-> (S == ~Ci)
    );

    // When A is all ones and B is zero, sum equals ~Ci.
    check_sum_when_a_allones_b_zero: assert property (
        @(posedge clk) ((A == 4'b1111) && (B == 4'b0000)) |-> (S == ~Ci)
    );
endmodule

module Adder4bit_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] S,
    input logic Co
);
    // Sum vector equals A + B.
    check_sum_vector_add: assert property (
        @(posedge clk) S == (A + B)
    );

    // Carry-out equals carry from the MSB stage.
    check_carry_out: assert property (
        @(posedge clk) Co == ((A[3] & B[3]) | ((A[3] ^ B[3]) & 1'b1))
    );

    // When A is zero, sum equals B.
    check_sum_when_a_zero: assert property (
        @(posedge clk) (A == 4'b0000) |-> (S == B)
    );

    // When B is zero, sum equals A.
    check_sum_when_b_zero: assert property (
        @(posedge clk) (B == 4'b0000) |-> (S == A)
    );

    // When A is all ones, sum equals ~B.
    check_sum_when_a_allones: assert property (
        @(posedge clk) (A == 4'b1111) |-> (S == ~B)
    );

    // When B is all ones, sum equals ~A.
    check_sum_when_b_allones: assert property (
        @(posedge clk) (B == 4'b1111) |-> (S == ~A)
    );

    // When A and B are zero, sum is zero.
    check_sum_when_ab_zero: assert property (
        @(posedge clk) ((A == 4'b0000) && (B == 4'b0000)) |-> (S == 4'b0000)
    );

    // When A and B are all ones, sum is all ones.
    check_sum_when_ab_allones: assert property (
        @(posedge clk) ((A == 4'b1111) && (B == 4'b1111)) |-> (S == 4'b1111)
    );

    // When A is zero and B is all ones, sum is all ones.
    check_sum_when_a_zero_b_allones: assert property (
        @(posedge clk) ((A == 4'b0000) && (B == 4'b1111)) |-> (S == 4'b1111)
   