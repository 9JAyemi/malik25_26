module or_gate_sva (
    input logic CLK,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic X
);
    ///// Functional correctness /////
    // X equals bitwise OR of all inputs.
    check_or_equivalence: assert property (
        @(posedge CLK) X === (A | B | C | D)
    );

    // When all inputs are 0, X must be 0.
    check_all_zero_implies_x_zero: assert property (
        @(posedge CLK) ((A == 1'b0) && (B == 1'b0) && (C == 1'b0) && (D == 1'b0)) |-> (X == 1'b0)
    );

    // If any input is 1, X must be 1.
    check_any_one_implies_x_one: assert property (
        @(posedge CLK) (A || B || C || D) |-> (X == 1'b1)
    );

    // If X is 0, all inputs must be 0.
    check_x_zero_implies_all_zero: assert property (
        @(posedge CLK) (X == 1'b0) |-> ((A == 1'b0) && (B == 1'b0) && (C == 1'b0) && (D == 1'b0))
    );

    // If X is 1, at least one input must be 1.
    check_x_one_implies_any_one: assert property (
        @(posedge CLK) (X == 1'b1) |-> (A || B || C || D)
    );

    ///// Stability and dependency /////
    // With stable inputs, X must remain stable.
    check_stable_inputs_implies_stable_x: assert property (
        @(posedge CLK) $stable({A,B,C,D}) |-> $stable(X)
    );

    // If X changes, at least one input must have changed.
    check_x_change_implies_input_change: assert property (
        @(posedge CLK) !$stable(X) |-> !$stable({A,B,C,D})
    );

    ///// Individual input dominance when others are 0 /////
    // With B,C,D=0, X must equal A.
    check_dom_a_when_others_zero: assert property (
        @(posedge CLK) ((B == 1'b0) && (C == 1'b0) && (D == 1'b0)) |-> (X === A)
    );

    // With A,C,D=0, X must equal B.
    check_dom_b_when_others_zero: assert property (
        @(posedge CLK) ((A == 1'b0) && (C == 1'b0) && (D == 1'b0)) |-> (X === B)
    );

    // With A,B,D=0, X must equal C.
    check_dom_c_when_others_zero: assert property (
        @(posedge CLK) ((A == 1'b0) && (B == 1'b0) && (D == 1'b0)) |-> (X === C)
    );

    // With A,B,C=0, X must equal D.
    check_dom_d_when_others_zero: assert property (
        @(posedge CLK) ((A == 1'b0) && (B == 1'b0) && (C == 1'b0)) |-> (X === D)
    );

endmodule