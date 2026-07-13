module and3_not_A_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic X
);
    // X must equal (~A) & B & C.
    check_functional_equivalence: assert property (
        @($global_clock) X == ((~A) & B & C)
    );

    // A=1 forces X=0.
    check_A_high_forces_X_low: assert property (
        @($global_clock) (A == 1'b1) |-> (X == 1'b0)
    );

    // B=0 forces X=0.
    check_B_low_forces_X_low: assert property (
        @($global_clock) (B == 1'b0) |-> (X == 1'b0)
    );

    // C=0 forces X=0.
    check_C_low_forces_X_low: assert property (
        @($global_clock) (C == 1'b0) |-> (X == 1'b0)
    );

    // A=0 and B=1 and C=1 forces X=1.
    check_inputs_set_force_X_high: assert property (
        @($global_clock) ((A == 1'b0) && (B == 1'b1) && (C == 1'b1)) |-> (X == 1'b1)
    );

    // When B=1 and C=1, X tracks ~A.
    check_X_tracks_notA_when_BC_high: assert property (
        @($global_clock) ((B == 1'b1) && (C == 1'b1)) |-> (X == (~A))
    );

    // A rising X requires A=0, B=1, C=1 in that cycle.
    check_rose_X_requires_inputs: assert property (
        @($global_clock) $rose(X) |-> ((A == 1'b0) && (B == 1'b1) && (C == 1'b1))
    );

    // A falling X requires A=1 or B=0 or C=0 in that cycle.
    check_fell_X_requires_cause: assert property (
        @($global_clock) $fell(X) |-> ((A == 1'b1) || (B == 1'b0) || (C == 1'b0))
    );

    // If A,B,C are stable across a cycle, X must also be stable.
    check_stability_follows_inputs: assert property (
        @($global_clock) ($stable(A) && $stable(B) && $stable(C)) |-> $stable(X)
    );
endmodule