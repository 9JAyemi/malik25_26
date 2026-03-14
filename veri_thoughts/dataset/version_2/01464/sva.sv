module sky130_fd_sc_hdll__o211a_sva (
    input logic CLK,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1
);
    ///// Functional correctness of X /////
    // X must equal (A1 | A2) & B1 & C1.
    check_functional_equivalence: assert property (
        @(posedge CLK) disable iff (1'b0) X == ((A1 | A2) & B1 & C1)
    );

    ///// Necessary conditions for X HIGH /////
    // If X is HIGH, then B1 must be HIGH.
    check_x_implies_b1: assert property (
        @(posedge CLK) disable iff (1'b0) (X == 1'b1) |-> (B1 == 1'b1)
    );
    // If X is HIGH, then C1 must be HIGH.
    check_x_implies_c1: assert property (
        @(posedge CLK) disable iff (1'b0) (X == 1'b1) |-> (C1 == 1'b1)
    );
    // If X is HIGH, then at least one of A1 or A2 must be HIGH.
    check_x_implies_a1_or_a2: assert property (
        @(posedge CLK) disable iff (1'b0) (X == 1'b1) |-> ((A1 == 1'b1) || (A2 == 1'b1))
    );

    ///// Sufficient conditions for X LOW /////
    // If B1 is LOW, X must be LOW.
    check_b1_zero_forces_x_zero: assert property (
        @(posedge CLK) disable iff (1'b0) (B1 == 1'b0) |-> (X == 1'b0)
    );
    // If C1 is LOW, X must be LOW.
    check_c1_zero_forces_x_zero: assert property (
        @(posedge CLK) disable iff (1'b0) (C1 == 1'b0) |-> (X == 1'b0)
    );
    // If both A1 and A2 are LOW, X must be LOW.
    check_neither_a1_nor_a2_forces_x_zero: assert property (
        @(posedge CLK) disable iff (1'b0) ((A1 == 1'b0) && (A2 == 1'b0)) |-> (X == 1'b0)
    );

    ///// Sufficient conditions for X HIGH /////
    // If B1 and C1 are HIGH and A1 is HIGH, X must be HIGH.
    check_b1_c1_a1_high_forces_x_high: assert property (
        @(posedge CLK) disable iff (1'b0) ((B1 == 1'b1) && (C1 == 1'b1) && (A1 == 1'b1)) |-> (X == 1'b1)
    );
    // If B1 and C1 are HIGH and A2 is HIGH, X must be HIGH.
    check_b1_c1_a2_high_forces_x_high: assert property (
        @(posedge CLK) disable iff (1'b0) ((B1 == 1'b1) && (C1 == 1'b1) && (A2 == 1'b1)) |-> (X == 1'b1)
    );

    ///// Output transition conditions /////
    // X can only rise when B1, C1, and (A1 or A2) are HIGH.
    check_x_rise_requires_inputs_true: assert property (
        @(posedge CLK) disable iff (1'b0) $rose(X) |-> ((B1 == 1'b1) && (C1 == 1'b1) && ((A1 == 1'b1) || (A2 == 1'b1)))
    );
    // X can only fall when at least one of B1, C1, or (A1 or A2) is LOW.
    check_x_fall_requires_any_input_false: assert property (
        @(posedge CLK) disable iff (1'b0) $fell(X) |-> ((B1 == 1'b0) || (C1 == 1'b0) || (((A1 == 1'b0) && (A2 == 1'b0))))
    );

    ///// Combinational stability /////
    // If inputs are stable across a cycle, X must be stable.
    check_stable_inputs_imply_stable_x: assert property (
        @(posedge CLK) disable iff (1'b0) $stable({A1, A2, B1, C1}) |-> $stable(X)
    );
endmodule