module logic_module_sva (
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic X
);
    // No clock/reset in RTL; pure combinational: X = (A1 & A2) | (B1 & B2).
    // Sample on any edge of inputs or X; no reset gating available.

    // X matches the defined combinational function of inputs.
    check_function_equivalence: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge B2 or negedge B2 or posedge X or negedge X)
            (X == ((A1 & A2) | (B1 & B2)))
    );

    // When neither pair (A1&A2) nor (B1&B2) is asserted, X must be 0.
    check_zero_when_neither_pair_high: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge B2 or negedge B2 or posedge X or negedge X)
            (!(A1 && A2) && !(B1 && B2)) |-> (X == 1'b0)
    );

    // When A1&A2 are both 1, X must be 1.
    check_one_when_A_pair_high: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge B2 or negedge B2 or posedge X or negedge X)
            (A1 && A2) |-> (X == 1'b1)
    );

    // When B1&B2 are both 1, X must be 1.
    check_one_when_B_pair_high: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge B2 or negedge B2 or posedge X or negedge X)
            (B1 && B2) |-> (X == 1'b1)
    );

    // If X is 1, at least one pair (A1&A2) or (B1&B2) must be 1.
    check_one_implies_some_pair_high: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge B2 or negedge B2 or posedge X or negedge X)
            (X == 1'b1) |-> ((A1 && A2) || (B1 && B2))
    );

    // If X is 0, neither (A1&A2) nor (B1&B2) can be 1.
    check_zero_implies_no_pairs_high: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge B2 or negedge B2 or posedge X or negedge X)
            (X == 1'b0) |-> (!(A1 && A2) && !(B1 && B2))
    );

    // With all inputs stable, X must remain stable (combinational dependency).
    check_output_stable_if_inputs_stable: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge B2 or negedge B2 or posedge X or negedge X)
            ($stable(A1) && $stable(A2) && $stable(B1) && $stable(B2)) |-> $stable(X)
    );

    // Rising assertion of A1&A2 forces X to 1 immediately.
    check_rose_Apair_sets_X: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge B2 or negedge B2 or posedge X or negedge X)
            $rose(A1 && A2) |-> (X == 1'b1)
    );

    // Rising assertion of B1&B2 forces X to 1 immediately.
    check_rose_Bpair_sets_X: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge B2 or negedge B2 or posedge X or negedge X)
            $rose(B1 && B2) |-> (X == 1'b1)
    );

    // Falling deassertion of A1&A2 clears X if B1&B2 are not asserted.
    check_fall_Apair_clears_X_if_Bpair_low: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge B2 or negedge B2 or posedge X or negedge X)
            ($fell(A1 && A2) && !(B1 && B2)) |-> (X == 1'b0)
    );

    // Falling deassertion of B1&B2 clears X if A1&A2 are not asserted.
    check_fall_Bpair_clears_X_if_Apair_low: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge B2 or negedge B2 or posedge X or negedge X)
            ($fell(B1 && B2) && !(A1 && A2)) |-> (X == 1'b0)
    );
endmodule