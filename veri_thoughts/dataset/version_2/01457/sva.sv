module sky130_fd_sc_hdll__or2_sva (
    input logic X,
    input logic A,
    input logic B
);
    // Output equals A OR B.
    check_or_equivalence: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge X or negedge X) disable iff (1'b0)
            X == (A | B)
    );

    // When both inputs are 0, output is 0.
    check_zero_case: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge X or negedge X) disable iff (1'b0)
            (!A && !B) |-> (X == 1'b0)
    );

    // If A is 1, output is 1.
    check_A_high_implies_X_high: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge X or negedge X) disable iff (1'b0)
            (A == 1'b1) |-> (X == 1'b1)
    );

    // If B is 1, output is 1.
    check_B_high_implies_X_high: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge X or negedge X) disable iff (1'b0)
            (B == 1'b1) |-> (X == 1'b1)
    );

    // If X is 0, both inputs must be 0.
    check_X_low_implies_inputs_low: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge X or negedge X) disable iff (1'b0)
            (X == 1'b0) |-> (!A && !B)
    );

    // If X is 1, at least one input is 1.
    check_X_high_implies_some_input_high: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge X or negedge X) disable iff (1'b0)
            (X == 1'b1) |-> (A || B)
    );

    // When A is 0, X equals B (OR identity).
    check_identity_A_zero: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge X or negedge X) disable iff (1'b0)
            (A == 1'b0) |-> (X == B)
    );

    // When B is 0, X equals A (OR identity).
    check_identity_B_zero: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge X or negedge X) disable iff (1'b0)
            (B == 1'b0) |-> (X == A)
    );

    // If inputs are stable, output remains stable.
    check_stable_inputs_imply_stable_output: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge X or negedge X) disable iff (1'b0)
            $stable({A,B}) |-> $stable(X)
    );

    // Output can only change if at least one input changed.
    check_output_change_requires_input_change: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge X or negedge X) disable iff (1'b0)
            $changed(X) |-> ($changed(A) || $changed(B))
    );
endmodule