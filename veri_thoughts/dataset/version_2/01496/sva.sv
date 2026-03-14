module sky130_fd_sc_lp__and2_sva (
    input logic CLK,   // external clock for sampling assertions
    input logic X,     // DUT output
    input logic A,     // DUT input
    input logic B      // DUT input
);
    // DUT has no clock/reset; pure combinational AND: X = A & B; assertions sampled on CLK.

    // X equals A & B every sampled cycle.
    check_functional_and: assert property (
        @(posedge CLK) X == (A & B)
    );

    // If X is 1, both inputs must be 1.
    check_x_one_implies_inputs_one: assert property (
        @(posedge CLK) X |-> (A && B)
    );

    // If both inputs are 1, X must be 1.
    check_inputs_one_implies_x_one: assert property (
        @(posedge CLK) (A && B) |-> X
    );

    // If A is 0, X must be 0.
    check_a_zero_forces_x_zero: assert property (
        @(posedge CLK) (A == 1'b0) |-> (X == 1'b0)
    );

    // If B is 0, X must be 0.
    check_b_zero_forces_x_zero: assert property (
        @(posedge CLK) (B == 1'b0) |-> (X == 1'b0)
    );

    // X can only rise when both inputs are 1.
    check_x_rise_requires_both_one: assert property (
        @(posedge CLK) $rose(X) |-> (A && B)
    );

    // X can only fall when at least one input is 0.
    check_x_fall_requires_any_zero: assert property (
        @(posedge CLK) $fell(X) |-> (!A || !B)
    );

    // If both inputs are stable, X must be stable.
    check_inputs_stable_implies_x_stable: assert property (
        @(posedge CLK) $stable(A) && $stable(B) |-> $stable(X)
    );

    // When A rises with B=1, X must be 1 that cycle.
    check_a_rise_with_b1_implies_x1: assert property (
        @(posedge CLK) $rose(A) && (B == 1'b1) |-> (X == 1'b1)
    );

    // When A falls with B=1, X must be 0 that cycle.
    check_a_fall_with_b1_implies_x0: assert property (
        @(posedge CLK) $fell(A) && (B == 1'b1) |-> (X == 1'b0)
    );

endmodule