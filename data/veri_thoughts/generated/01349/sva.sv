module sky130_fd_sc_ms__a21oi_sva (
    input  logic CLK,
    input  logic Y,
    input  logic A1,
    input  logic A2,
    input  logic B1
);
    // Functional equivalence: Y = ~(B1 | (A1 & A2)).
    check_functional_equation: assert property (
        @(posedge CLK) Y == ~(B1 | (A1 & A2))
    );

    // Y must be 1 when B1 is 0 and (A1 & A2) is 0.
    check_y_high_when_b1_low_and_and_low: assert property (
        @(posedge CLK) (!B1 && !(A1 & A2)) |-> (Y == 1'b1)
    );

    // Y must be 0 when B1 is 1.
    check_y_low_when_b1_high: assert property (
        @(posedge CLK) B1 |-> (Y == 1'b0)
    );

    // Y must be 0 when both A1 and A2 are 1.
    check_y_low_when_a1_and_a2_high: assert property (
        @(posedge CLK) (A1 && A2) |-> (Y == 1'b0)
    );

    // When A1 is 0, Y equals ~B1.
    check_y_eq_not_b1_when_a1_zero: assert property (
        @(posedge CLK) (!A1) |-> (Y == ~B1)
    );

    // When A2 is 0, Y equals ~B1.
    check_y_eq_not_b1_when_a2_zero: assert property (
        @(posedge CLK) (!A2) |-> (Y == ~B1)
    );

    // If Y is 1, then B1 must be 0.
    check_y_high_implies_b1_low: assert property (
        @(posedge CLK) (Y == 1'b1) |-> (!B1)
    );

    // If Y is 1, at least one of A1 or A2 must be 0.
    check_y_high_implies_not_both_as_high: assert property (
        @(posedge CLK) (Y == 1'b1) |-> ((!A1) || (!A2))
    );

    // If Y is 0, then B1 is 1 or (A1 & A2) is 1.
    check_y_low_causes: assert property (
        @(posedge CLK) (Y == 1'b0) |-> (B1 || (A1 & A2))
    );

    // If inputs are stable across a cycle, output must be stable.
    check_stable_inputs_imply_stable_output: assert property (
        @(posedge CLK) $stable({A1, A2, B1}) |-> $stable(Y)
    );
endmodule