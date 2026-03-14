module sky130_fd_sc_ms__and3_sva (
    input logic X,
    input logic A,
    input logic B,
    input logic C
);
    // Analysis: No clock or reset in DUT; purely combinational; X = A & B & C.

    // Functional equivalence sampled on A rising.
    check_func_on_A_edge: assert property (
        @(posedge A) X == (A & B & C)
    );

    // Functional equivalence sampled on B rising.
    check_func_on_B_edge: assert property (
        @(posedge B) X == (A & B & C)
    );

    // Functional equivalence sampled on C rising.
    check_func_on_C_edge: assert property (
        @(posedge C) X == (A & B & C)
    );

    // Functional equivalence sampled on X rising.
    check_func_on_X_edge: assert property (
        @(posedge X) X == (A & B & C)
    );

    // If X is HIGH, all inputs must be HIGH.
    check_x_high_implies_inputs_high: assert property (
        @(posedge X) X |-> (A && B && C)
    );

    // Any rise of X must be due to some input change.
    check_x_rise_requires_input_change: assert property (
        @(posedge X) 1'b1 |-> ($changed(A) || $changed(B) || $changed(C))
    );

    // When A rises and B,C are stably 1, X must rise.
    check_x_rose_on_A_when_BC_ones: assert property (
        @(posedge A) (B && C && $past(B) && $past(C)) |-> $rose(X)
    );

    // When B rises and A,C are stably 1, X must rise.
    check_x_rose_on_B_when_AC_ones: assert property (
        @(posedge B) (A && C && $past(A) && $past(C)) |-> $rose(X)
    );

    // When C rises and A,B are stably 1, X must rise.
    check_x_rose_on_C_when_AB_ones: assert property (
        @(posedge C) (A && B && $past(A) && $past(B)) |-> $rose(X)
    );

endmodule