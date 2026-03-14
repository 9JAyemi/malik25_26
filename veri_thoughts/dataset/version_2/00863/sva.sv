module sky130_fd_sc_hd__or4b_sva (
    input logic CLK,   // Sampling clock for assertions (RTL has no clock/reset)
    input logic A,
    input logic B,
    input logic C,
    input logic D_N,
    input logic X
);
    ///// Functional equivalence /////
    // X implements a 4-input NAND of {A,B,C,D_N}.
    check_functional_equation: assert property (
        @(posedge CLK) X == ~(A & B & C & D_N)
    );

    ///// Basic implications /////
    // When all inputs are 1, X must be 0.
    check_all_ones_implies_X0: assert property (
        @(posedge CLK) (A && B && C && D_N) |-> (X == 1'b0)
    );
    // If A is 0, X must be 1.
    check_A_zero_implies_X1: assert property (
        @(posedge CLK) (!A) |-> (X == 1'b1)
    );
    // If B is 0, X must be 1.
    check_B_zero_implies_X1: assert property (
        @(posedge CLK) (!B) |-> (X == 1'b1)
    );
    // If C is 0, X must be 1.
    check_C_zero_implies_X1: assert property (
        @(posedge CLK) (!C) |-> (X == 1'b1)
    );
    // If D_N is 0, X must be 1.
    check_DN_zero_implies_X1: assert property (
        @(posedge CLK) (!D_N) |-> (X == 1'b1)
    );

    ///// Output transition constraints /////
    // X can only fall when all inputs are 1 in the same cycle.
    check_X_fall_implies_all_ones: assert property (
        @(posedge CLK) $fell(X) |-> (A && B && C && D_N)
    );
    // X can only rise when at least one input is 0 in the same cycle.
    check_X_rise_implies_any_zero: assert property (
        @(posedge CLK) $rose(X) |-> (!A || !B || !C || !D_N)
    );

    ///// Input transition effects under enabling conditions /////
    // If A rises while B,C,D_N are 1, X must fall.
    check_rise_A_others1_causes_X_fall: assert property (
        @(posedge CLK) (B && C && D_N && $rose(A)) |-> $fell(X)
    );
    // If B rises while A,C,D_N are 1, X must fall.
    check_rise_B_others1_causes_X_fall: assert property (
        @(posedge CLK) (A && C && D_N && $rose(B)) |-> $fell(X)
    );
    // If C rises while A,B,D_N are 1, X must fall.
    check_rise_C_others1_causes_X_fall: assert property (
        @(posedge CLK) (A && B && D_N && $rose(C)) |-> $fell(X)
    );
    // If D_N rises while A,B,C are 1, X must fall.
    check_rise_DN_others1_causes_X_fall: assert property (
        @(posedge CLK) (A && B && C && $rose(D_N)) |-> $fell(X)
    );
endmodule