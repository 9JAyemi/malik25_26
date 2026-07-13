module OAI22X1_sva (
    input  logic CLK,   // External clock for SVA (RTL is combinational, no reset)
    input  logic A,
    input  logic B,
    input  logic C,
    input  logic Y
);
    // Y implements Y = C & (~A | ~B).
    check_functional_equivalence: assert property (
        @(posedge CLK) Y == (C & ((~A) | (~B)))
    );

    // Y can only be 1 when C is 1.
    check_y_implies_c: assert property (
        @(posedge CLK) Y |-> C
    );

    // C=0 forces Y=0.
    check_c0_forces_y0: assert property (
        @(posedge CLK) (!C) |-> (Y == 1'b0)
    );

    // If both A and B are 1, Y must be 0 (independent of C).
    check_ab_both_one_forces_y0: assert property (
        @(posedge CLK) (A && B) |-> (Y == 1'b0)
    );

    // With C=1 and A=0, Y must be 1.
    check_c1_a0_sets_y1: assert property (
        @(posedge CLK) (C && !A) |-> (Y == 1'b1)
    );

    // With C=1 and B=0, Y must be 1.
    check_c1_b0_sets_y1: assert property (
        @(posedge CLK) (C && !B) |-> (Y == 1'b1)
    );

    // If Y=1, then C=1 and at least one of A or B is 0.
    check_y1_implies_c_and_one_input_zero: assert property (
        @(posedge CLK) Y |-> (C && ((!A) || (!B)))
    );
endmodule