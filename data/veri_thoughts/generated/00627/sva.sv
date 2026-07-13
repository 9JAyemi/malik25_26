module sky130_fd_sc_lp__or4b_sva (
    input logic CLK,
    input logic X,
    input logic A,
    input logic B,
    input logic C,
    input logic D_N
);
    // Functional equivalence: X is OR of A,B,C and inverted D_N.
    check_functional_equivalence: assert property (
        @(posedge CLK) X == (A | B | C | ~D_N)
    );

    // If any input asserts (A/B/C) or D_N deasserts (0), X must be 1.
    check_any_input_high_implies_x_high: assert property (
        @(posedge CLK) ((A == 1'b1) || (B == 1'b1) || (C == 1'b1) || (D_N == 1'b0)) |-> (X == 1'b1)
    );

    // The only case for X to be 0 is A=B=C=0 and D_N=1.
    check_only_case_for_x_low: assert property (
        @(posedge CLK) ((A == 1'b0) && (B == 1'b0) && (C == 1'b0) && (D_N == 1'b1)) |-> (X == 1'b0)
    );

    // If X is 0, inputs must be A=B=C=0 and D_N=1.
    check_x_low_implies_inputs_zero: assert property (
        @(posedge CLK) (X == 1'b0) |-> ((A == 1'b0) && (B == 1'b0) && (C == 1'b0) && (D_N == 1'b1))
    );

    // If X is 1, at least one of A/B/C is 1 or D_N is 0.
    check_x_high_implies_some_input_high: assert property (
        @(posedge CLK) (X == 1'b1) |-> ((A == 1'b1) || (B == 1'b1) || (C == 1'b1) || (D_N == 1'b0))
    );

    // A high alone is sufficient to drive X high.
    check_a_high_drives_x: assert property (
        @(posedge CLK) (A == 1'b1) |-> (X == 1'b1)
    );

    // B high alone is sufficient to drive X high.
    check_b_high_drives_x: assert property (
        @(posedge CLK) (B == 1'b1) |-> (X == 1'b1)
    );

    // C high alone is sufficient to drive X high.
    check_c_high_drives_x: assert property (
        @(posedge CLK) (C == 1'b1) |-> (X == 1'b1)
    );

    // D_N low (active low) alone is sufficient to drive X high.
    check_dn_low_drives_x: assert property (
        @(posedge CLK) (D_N == 1'b0) |-> (X == 1'b1)
    );

    // Output is stable across cycles when all inputs are stable.
    check_stability_when_inputs_stable: assert property (
        @(posedge CLK) ($stable(A) && $stable(B) && $stable(C) && $stable(D_N)) |-> $stable(X)
    );
endmodule