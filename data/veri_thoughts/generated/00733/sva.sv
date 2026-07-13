module or4_module_sva (
    input logic CLK,     // Sampling clock for assertions (DUT has no clock)
    input logic A,
    input logic B,
    input logic C_N,
    input logic D_N,
    input logic X
);
    // Clocks: none in RTL; Resets: none; Logic: pure combinational X = A | B | ~C_N | ~D_N.

    // X equals the defined OR function of inputs.
    check_or_function: assert property (
        @(posedge CLK) disable iff (1'b0) X == (A | B | ~C_N | ~D_N)
    );

    // Rising A drives X HIGH in the same cycle.
    check_rose_A_sets_X_high: assert property (
        @(posedge CLK) disable iff (1'b0) $rose(A) |-> X
    );

    // Rising B drives X HIGH in the same cycle.
    check_rose_B_sets_X_high: assert property (
        @(posedge CLK) disable iff (1'b0) $rose(B) |-> X
    );

    // Falling C_N (active-low) drives X HIGH in the same cycle.
    check_fell_C_N_sets_X_high: assert property (
        @(posedge CLK) disable iff (1'b0) $fell(C_N) |-> X
    );

    // Falling D_N (active-low) drives X HIGH in the same cycle.
    check_fell_D_N_sets_X_high: assert property (
        @(posedge CLK) disable iff (1'b0) $fell(D_N) |-> X
    );

    // When all inputs are inactive (A=0,B=0,C_N=1,D_N=1), X must be LOW.
    check_all_inactive_makes_X_low: assert property (
        @(posedge CLK) disable iff (1'b0) (!A && !B && C_N && D_N) |-> !X
    );

    // If X is LOW, then all inputs must be inactive (A=0,B=0,C_N=1,D_N=1).
    check_X_low_means_all_inactive: assert property (
        @(posedge CLK) disable iff (1'b0) (!X) |-> (!A && !B && C_N && D_N)
    );

    // If X is HIGH, at least one driving condition must be true.
    check_X_high_has_some_cause: assert property (
        @(posedge CLK) disable iff (1'b0) X |-> (A || B || !C_N || !D_N)
    );

    // Output cannot change if all inputs are stable.
    check_output_stable_when_inputs_stable: assert property (
        @(posedge CLK) disable iff (1'b0) ($stable(A) && $stable(B) && $stable(C_N) && $stable(D_N)) |-> $stable(X)
    );

    // If A and B are 0, X equals (~C_N | ~D_N).
    check_AB_zero_refines_X: assert property (
        @(posedge CLK) disable iff (1'b0) (!A && !B) |-> (X == (~C_N | ~D_N))
    );
endmodule