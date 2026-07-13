module sky130_fd_sc_ms__and3b_sva (
    input logic clk,   // sampling clock for assertions
    input logic X,
    input logic A_N,
    input logic B,
    input logic C
);
    // Output equals B & C & ~A_N.
    check_functional_equivalence: assert property (
        @(posedge clk) X == (B & C & ~A_N)
    );

    // A_N high forces X low.
    check_A_N_high_forces_low: assert property (
        @(posedge clk) (A_N == 1'b1) |-> (X == 1'b0)
    );

    // B low forces X low.
    check_B_low_forces_low: assert property (
        @(posedge clk) (B == 1'b0) |-> (X == 1'b0)
    );

    // C low forces X low.
    check_C_low_forces_low: assert property (
        @(posedge clk) (C == 1'b0) |-> (X == 1'b0)
    );

    // When all enables are asserted (A_N=0,B=1,C=1) output is high.
    check_all_inputs_enable_high: assert property (
        @(posedge clk) ((A_N == 1'b0) && (B == 1'b1) && (C == 1'b1)) |-> (X == 1'b1)
    );

    // X high implies A_N=0, B=1, and C=1.
    check_X_high_implies_inputs: assert property (
        @(posedge clk) (X == 1'b1) |-> ((A_N == 1'b0) && (B == 1'b1) && (C == 1'b1))
    );

    // If B and C are high, X equals ~A_N.
    check_when_BC_high_X_eq_notA: assert property (
        @(posedge clk) ((B == 1'b1) && (C == 1'b1)) |-> (X == ~A_N)
    );

    // If C and ~A_N are high, X equals B.
    check_when_C_and_notA_X_eq_B: assert property (
        @(posedge clk) ((C == 1'b1) && (A_N == 1'b0)) |-> (X == B)
    );

    // If B and ~A_N are high, X equals C.
    check_when_B_and_notA_X_eq_C: assert property (
        @(posedge clk) ((B == 1'b1) && (A_N == 1'b0)) |-> (X == C)
    );

    // X rising requires B=1, C=1, and A_N=0.
    check_rose_X_requires_enable: assert property (
        @(posedge clk) $rose(X) |-> ((B == 1'b1) && (C == 1'b1) && (A_N == 1'b0))
    );

    // X falling requires !(B & C & ~A_N).
    check_fell_X_requires_not_condition: assert property (
        @(posedge clk) $fell(X) |-> !((B == 1'b1) && (C == 1'b1) && (A_N == 1'b0))
    );
endmodule