module sky130_fd_sc_lp__iso0p_sva (
    input logic X,
    input logic A,
    input logic SLEEP
);
    // X equals A & ~SLEEP on any A edge.
    check_function_on_A_edges: assert property (
        @(posedge A or negedge A) (X == (A & ~SLEEP))
    );
    // X equals A & ~SLEEP on any SLEEP edge.
    check_function_on_SLEEP_edges: assert property (
        @(posedge SLEEP or negedge SLEEP) (X == (A & ~SLEEP))
    );
    // X equals A & ~SLEEP on any X edge.
    check_function_on_X_edges: assert property (
        @(posedge X or negedge X) (X == (A & ~SLEEP))
    );
    // When SLEEP is HIGH, X must be 0 on A edges.
    check_clamp_when_sleep_high_on_A_edges: assert property (
        @(posedge A or negedge A) (SLEEP == 1'b1) |-> (X == 1'b0)
    );
    // When SLEEP is LOW, X equals A on A edges.
    check_transparency_when_sleep_low_on_A_edges: assert property (
        @(posedge A or negedge A) (SLEEP == 1'b0) |-> (X == A)
    );
    // Asserting SLEEP clamps X LOW immediately.
    check_sleep_rise_clamps_low: assert property (
        @(posedge SLEEP) (X == 1'b0)
    );
    // Deasserting SLEEP makes X equal to A immediately.
    check_sleep_fall_transparent: assert property (
        @(negedge SLEEP) (X == A)
    );
    // With SLEEP LOW, a rising A causes a rising X.
    check_rose_A_causes_rose_X_when_sleep_low: assert property (
        @(posedge A) (SLEEP == 1'b0) |-> $rose(X)
    );
    // With SLEEP LOW, a falling A causes a falling X.
    check_fell_A_causes_fell_X_when_sleep_low: assert property (
        @(negedge A) (SLEEP == 1'b0) |-> $fell(X)
    );
    // X can only be HIGH if A is HIGH and SLEEP is LOW (on input edges).
    check_output_high_conditions: assert property (
        @(posedge A or negedge A or posedge SLEEP or negedge SLEEP) (X == 1'b1) |-> ((A == 1'b1) && (SLEEP == 1'b0))
    );
endmodule