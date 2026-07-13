module adder_subtractor_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic SUB,
    input logic [3:0] SUM
);
    // SUM matches the RTL expression for both add and subtract paths (modulo 16).
    functional_equivalence_to_rtl: assert property (
        @(posedge clk) SUM == ( SUB
            ? (({1'b0, A} + ({1'b0, ~B} + 5'd1)) [3:0])
            : (({1'b0, A} + {1'b0, B}) [3:0]) )
    );

    // When SUB=0, SUM is low 4 bits of A+B.
    add_path_correct: assert property (
        @(posedge clk) (SUB == 1'b0) |-> (SUM == (({1'b0, A} + {1'b0, B}) [3:0]))
    );

    // When SUB=1, SUM is low 4 bits of A+(~B+1).
    sub_path_correct: assert property (
        @(posedge clk) (SUB == 1'b1) |-> (SUM == (({1'b0, A} + ({1'b0, ~B} + 5'd1)) [3:0]))
    );

    // If B is zero, SUM equals A regardless of SUB.
    identity_when_B_is_zero: assert property (
        @(posedge clk) (B == 4'd0) |-> (SUM == A)
    );

    // If A is zero and SUB=0, SUM equals B.
    add_identity_when_A_zero: assert property (
        @(posedge clk) (SUB == 1'b0 && A == 4'd0) |-> (SUM == B)
    );

    // If SUB=1 and A==B, SUM is zero (A - A = 0 modulo 16).
    subtract_equal_operands_zero: assert property (
        @(posedge clk) (SUB == 1'b1 && (A == B)) |-> (SUM == 4'd0)
    );

    // If SUB=1 and B=15, SUM equals A+1 modulo 16.
    sub_with_B_15_increments_A: assert property (
        @(posedge clk) (SUB == 1'b1 && B == 4'd15) |-> (SUM == (({1'b0, A} + 5'd1) [3:0]))
    );

    // If SUB=1 and B=8, SUM equals A+8 modulo 16 (since ~8+1 == 8 in 4-bit).
    sub_with_B_8_equals_add_8: assert property (
        @(posedge clk) (SUB == 1'b1 && B == 4'd8) |-> (SUM == (({1'b0, A} + 5'd8) [3:0]))
    );

    // If A, B, and SUB hold their values, SUM must hold as well (combinational behavior).
    stable_output_when_inputs_stable: assert property (
        @(posedge clk) $stable(A) && $stable(B) && $stable(SUB) |-> $stable(SUM)
    );
endmodule