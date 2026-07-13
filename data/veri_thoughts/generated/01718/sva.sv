module sky130_fd_sc_lp__a32o_sva (
    input logic CLK,
    input logic X,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic B2
);
    // X equals (A1 & A2 & A3) | (B1 & B2).
    check_function_equivalence: assert property (
        @(posedge CLK) X == ((A1 & A2 & A3) | (B1 & B2))
    );

    // A-path asserted forces X HIGH.
    check_A_path_sets_X: assert property (
        @(posedge CLK) (A1 & A2 & A3) |-> (X == 1'b1)
    );

    // B-path asserted forces X HIGH.
    check_B_path_sets_X: assert property (
        @(posedge CLK) (B1 & B2) |-> (X == 1'b1)
    );

    // X HIGH implies at least one path is TRUE.
    check_X_high_implies_cause: assert property (
        @(posedge CLK) (X == 1'b1) |-> ((A1 & A2 & A3) || (B1 & B2))
    );

    // When neither path is TRUE, X must be LOW.
    check_no_path_implies_X_low: assert property (
        @(posedge CLK) (!(A1 & A2 & A3) && !(B1 & B2)) |-> (X == 1'b0)
    );

    // If all inputs are stable, X must remain stable.
    check_stability_with_stable_inputs: assert property (
        @(posedge CLK) $stable(A1) && $stable(A2) && $stable(A3) && $stable(B1) && $stable(B2) |-> $stable(X)
    );

    // No spurious X rise when both paths are FALSE.
    check_no_spurious_rise: assert property (
        @(posedge CLK) (!(A1 & A2 & A3) && !(B1 & B2)) |-> !$rose(X)
    );

    // If any path is TRUE, X cannot fall this cycle.
    check_no_fall_when_path_true: assert property (
        @(posedge CLK) ((A1 & A2 & A3) || (B1 & B2)) |-> !$fell(X)
    );
endmodule