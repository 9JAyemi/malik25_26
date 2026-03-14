module sky130_fd_sc_hd__or2_sva (
    input logic CLK,
    input logic X,
    input logic A,
    input logic B
);
    // Output equals logical OR of inputs each cycle.
    check_or_function: assert property (
        @(posedge CLK) X == (A | B)
    );

    // When both inputs are 0, output must be 0.
    check_zero_zero_low: assert property (
        @(posedge CLK) (A == 1'b0 && B == 1'b0) |-> (X == 1'b0)
    );

    // If output is 1, at least one input must be 1.
    check_x_high_requires_input_high: assert property (
        @(posedge CLK) (X == 1'b1) |-> ((A == 1'b1) || (B == 1'b1))
    );

    // If A is 1, output must be 1.
    check_a_high_implies_x_high: assert property (
        @(posedge CLK) (A == 1'b1) |-> (X == 1'b1)
    );

    // If B is 1, output must be 1.
    check_b_high_implies_x_high: assert property (
        @(posedge CLK) (B == 1'b1) |-> (X == 1'b1)
    );

    // When B is 0, output follows A.
    check_follow_a_when_b_zero: assert property (
        @(posedge CLK) (B == 1'b0) |-> (X == A)
    );

    // When A is 0, output follows B.
    check_follow_b_when_a_zero: assert property (
        @(posedge CLK) (A == 1'b0) |-> (X == B)
    );

    // If inputs are stable, output remains stable.
    check_stable_inputs_keep_output_stable: assert property (
        @(posedge CLK) $stable(A) && $stable(B) |-> $stable(X)
    );

    // Output change implies at least one input changed.
    check_output_change_implies_input_change: assert property (
        @(posedge CLK) $changed(X) |-> ($changed(A) || $changed(B))
    );
endmodule