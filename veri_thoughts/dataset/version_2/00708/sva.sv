module sky130_fd_sc_ms__or4b_sva (
    input logic CLK,
    input logic RESETn,
    input logic X,
    input logic A,
    input logic B,
    input logic C,
    input logic D_N
);
    // X equals A|B|C|~D_N (truth function of the gate).
    check_function_equivalence: assert property (
        @(posedge CLK) disable iff (!RESETn) X == (A | B | C | ~D_N)
    );

    // A high forces X high.
    check_A_forces_high: assert property (
        @(posedge CLK) disable iff (!RESETn) (A == 1'b1) |-> (X == 1'b1)
    );

    // B high forces X high.
    check_B_forces_high: assert property (
        @(posedge CLK) disable iff (!RESETn) (B == 1'b1) |-> (X == 1'b1)
    );

    // C high forces X high.
    check_C_forces_high: assert property (
        @(posedge CLK) disable iff (!RESETn) (C == 1'b1) |-> (X == 1'b1)
    );

    // D_N low (i.e., ~D_N high) forces X high.
    check_DN_low_forces_high: assert property (
        @(posedge CLK) disable iff (!RESETn) (D_N == 1'b0) |-> (X == 1'b1)
    );

    // All inputs low and D_N high yield X low.
    check_all_low_results_low: assert property (
        @(posedge CLK) disable iff (!RESETn) ((A == 1'b0) && (B == 1'b0) && (C == 1'b0) && (D_N == 1'b1)) |-> (X == 1'b0)
    );

    // X low implies A,B,C are low and D_N is high.
    check_x_low_implies_inputs_low: assert property (
        @(posedge CLK) disable iff (!RESETn) (X == 1'b0) |-> ((A == 1'b0) && (B == 1'b0) && (C == 1'b0) && (D_N == 1'b1))
    );

    // If inputs do not change, X must not change (pure combinational).
    check_stable_if_inputs_stable: assert property (
        @(posedge CLK) disable iff (!RESETn) (!$changed(A) && !$changed(B) && !$changed(C) && !$changed(D_N)) |-> !$changed(X)
    );

    // If X changes, at least one input must have changed.
    check_x_change_implies_input_change: assert property (
        @(posedge CLK) disable iff (!RESETn) $changed(X) |-> ($changed(A) || $changed(B) || $changed(C) || $changed(D_N))
    );
endmodule