module custom_or3_sva (
    input logic clk,   // Sampling clock for SVA (no clock/reset in RTL)
    input logic A,
    input logic B,
    input logic C_N,
    input logic X
);
    // Analysis: No clock/reset in RTL; purely combinational; functionally X == (A | B | C_N).

    // X equals bitwise OR of inputs every cycle.
    check_or_function: assert property (
        @(posedge clk) X == (A | B | C_N)
    );

    // A high forces X high.
    check_A_high_implies_X_high: assert property (
        @(posedge clk) (A == 1'b1) |-> (X == 1'b1)
    );

    // B high forces X high.
    check_B_high_implies_X_high: assert property (
        @(posedge clk) (B == 1'b1) |-> (X == 1'b1)
    );

    // C_N high forces X high.
    check_C_N_high_implies_X_high: assert property (
        @(posedge clk) (C_N == 1'b1) |-> (X == 1'b1)
    );

    // All inputs low force X low.
    check_all_low_implies_X_low: assert property (
        @(posedge clk) (A == 1'b0 && B == 1'b0 && C_N == 1'b0) |-> (X == 1'b0)
    );

    // X low implies all inputs low.
    check_X_low_implies_all_low: assert property (
        @(posedge clk) (X == 1'b0) |-> (A == 1'b0 && B == 1'b0 && C_N == 1'b0)
    );

    // X high implies at least one input high.
    check_X_high_implies_any_high: assert property (
        @(posedge clk) (X == 1'b1) |-> (A == 1'b1 || B == 1'b1 || C_N == 1'b1)
    );

    // If inputs are stable, X is stable.
    check_inputs_stable_implies_X_stable: assert property (
        @(posedge clk) ($stable(A) && $stable(B) && $stable(C_N)) |-> $stable(X)
    );

    // X changes only if some input changes.
    check_X_change_implies_input_change: assert property (
        @(posedge clk) (X ^ $past(X)) |-> ((A ^ $past(A)) || (B ^ $past(B)) || (C_N ^ $past(C_N)))
    );

    // When B and C_N are low, X equals A.
    check_reduce_to_A_when_others_low: assert property (
        @(posedge clk) (B == 1'b0 && C_N == 1'b0) |-> (X == A)
    );

endmodule