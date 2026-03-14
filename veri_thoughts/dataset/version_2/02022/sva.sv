module sky130_fd_sc_hvl__or3_sva (
    input logic CLK,   // external verification clock (DUT has no clock/reset)
    input logic X,
    input logic A,
    input logic B,
    input logic C
);
    ///// OR3 functional correctness /////
    // X equals logical OR of A,B,C each cycle.
    check_or_function_equivalence: assert property (
        @(posedge CLK) (X == (A | B | C))
    );

    // If A is 1, X must be 1 the same cycle.
    check_a_high_forces_x_high: assert property (
        @(posedge CLK) (A == 1'b1) |-> (X == 1'b1)
    );

    // If B is 1, X must be 1 the same cycle.
    check_b_high_forces_x_high: assert property (
        @(posedge CLK) (B == 1'b1) |-> (X == 1'b1)
    );

    // If C is 1, X must be 1 the same cycle.
    check_c_high_forces_x_high: assert property (
        @(posedge CLK) (C == 1'b1) |-> (X == 1'b1)
    );

    // If all inputs are 0, X must be 0 the same cycle.
    check_all_zero_forces_x_zero: assert property (
        @(posedge CLK) ((A == 1'b0) && (B == 1'b0) && (C == 1'b0)) |-> (X == 1'b0)
    );

    // If X is 0, then all inputs must be 0.
    check_x_zero_implies_all_zero: assert property (
        @(posedge CLK) (X == 1'b0) |-> ((A == 1'b0) && (B == 1'b0) && (C == 1'b0))
    );

    ///// Combinational dependency /////
    // X can only change if at least one input changes.
    check_output_change_requires_input_change: assert property (
        @(posedge CLK) $changed(X) |-> ($changed(A) || $changed(B) || $changed(C))
    );
endmodule