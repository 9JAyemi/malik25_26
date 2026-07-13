module sky130_fd_sc_hvl__and2_sva (
    input logic X,
    input logic A,
    input logic B
);
    // Combinational AND gate; no clock/reset in RTL; sample on $global_clock.

    // Output equals A & B.
    check_and_function: assert property (
        @(posedge $global_clock) X == (A & B)
    );

    // If A is 0, X must be 0.
    check_zero_dominance_A: assert property (
        @(posedge $global_clock) (A == 1'b0) |-> (X == 1'b0)
    );

    // If B is 0, X must be 0.
    check_zero_dominance_B: assert property (
        @(posedge $global_clock) (B == 1'b0) |-> (X == 1'b0)
    );

    // If both A and B are 1, X must be 1.
    check_one_when_both_one: assert property (
        @(posedge $global_clock) (A == 1'b1 && B == 1'b1) |-> (X == 1'b1)
    );

    // If X is 1, both A and B must be 1.
    check_output_implies_inputs_high: assert property (
        @(posedge $global_clock) (X == 1'b1) |-> (A == 1'b1 && B == 1'b1)
    );

    // X rises when A rises and B is 1.
    check_rise_with_A_when_B_high: assert property (
        @(posedge $global_clock) $rose(A) && (B == 1'b1) |-> (X == 1'b1)
    );

    // X falls when A falls and B is 1.
    check_fall_with_A_when_B_high: assert property (
        @(posedge $global_clock) $fell(A) && (B == 1'b1) |-> (X == 1'b0)
    );

    // X rises when B rises and A is 1.
    check_rise_with_B_when_A_high: assert property (
        @(posedge $global_clock) $rose(B) && (A == 1'b1) |-> (X == 1'b1)
    );

    // X falls when B falls and A is 1.
    check_fall_with_B_when_A_high: assert property (
        @(posedge $global_clock) $fell(B) && (A == 1'b1) |-> (X == 1'b0)
    );

    // If A and B are stable, X is stable.
    check_stability_when_inputs_stable: assert property (
        @(posedge $global_clock) $stable(A) && $stable(B) |-> $stable(X)
    );

endmodule