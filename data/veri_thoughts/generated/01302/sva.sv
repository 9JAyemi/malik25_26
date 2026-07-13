module sky130_fd_sc_hdll__a2bb2o_sva (
    input logic clk,      // sampling clock (DUT is purely combinational)
    input logic X,
    input logic A1_N,
    input logic A2_N,
    input logic B1,
    input logic B2
);
    ///// Combinational function checks /////
    // X implements (~A1_N & ~A2_N) | (B1 & B2).
    check_functional_equivalence: assert property (
        @(posedge clk) X == ((~A1_N & ~A2_N) | (B1 & B2))
    );

    // When both A inputs are LOW, X must be HIGH.
    check_A_both_low_forces_high: assert property (
        @(posedge clk) (!A1_N && !A2_N) |-> (X == 1'b1)
    );

    // When both B inputs are HIGH, X must be HIGH.
    check_B_both_high_forces_high: assert property (
        @(posedge clk) (B1 && B2) |-> (X == 1'b1)
    );

    // If any A is HIGH and not both B are HIGH, X must be LOW.
    check_A_any_high_and_not_B_and_forces_low: assert property (
        @(posedge clk) ((A1_N || A2_N) && !(B1 && B2)) |-> (X == 1'b0)
    );

    // When both A inputs are HIGH, X equals (B1 & B2).
    check_A_both_high_equals_B_and: assert property (
        @(posedge clk) (A1_N && A2_N) |-> (X == (B1 & B2))
    );

    // When exactly one A is HIGH (A1_N ^ A2_N), X equals (B1 & B2).
    check_A_xor_equals_B_and: assert property (
        @(posedge clk) (A1_N ^ A2_N) |-> (X == (B1 & B2))
    );

    // If X is LOW, then at least one A is HIGH and not both B are HIGH.
    check_X_low_implies_inputs_state: assert property (
        @(posedge clk) (X == 1'b0) |-> ((A1_N || A2_N) && !(B1 && B2))
    );

    // If X is HIGH, then either both A are LOW or both B are HIGH.
    check_X_high_implies_inputs_state: assert property (
        @(posedge clk) (X == 1'b1) |-> ((!A1_N && !A2_N) || (B1 && B2))
    );

    // If all inputs are stable, X must be stable.
    check_stable_when_inputs_stable: assert property (
        @(posedge clk) ($stable(A1_N) && $stable(A2_N) && $stable(B1) && $stable(B2)) |-> $stable(X)
    );

    // If X changes, at least one input must have changed.
    check_X_change_requires_input_change: assert property (
        @(posedge clk) $changed(X) |-> ($changed(A1_N) || $changed(A2_N) || $changed(B1) || $changed(B2))
    );
endmodule