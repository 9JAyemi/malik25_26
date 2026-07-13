module karnaugh_map_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic E,
    input logic F
);
    // No clock/reset in RTL; pure combinational; assertions use the formal $global_clock.

    // For A=0, F equals NOT C regardless of B,D,E.
    check_a0_inverts_C: assert property (
        @($global_clock) (A == 1'b0) |-> (F == ~C)
    );

    // For A=1 and E=0, F equals C OR D.
    check_a1_e0_is_C_or_D: assert property (
        @($global_clock) (A == 1'b1 && E == 1'b0) |-> (F == (C || D))
    );

    // For A=1 and E=1, F equals NOT C AND NOT D.
    check_a1_e1_is_notC_and_notD: assert property (
        @($global_clock) (A == 1'b1 && E == 1'b1) |-> (F == (~C && ~D))
    );

    // B has no functional effect: with A,C,D,E stable, toggling B leaves F unchanged.
    check_B_independence_fixed_inputs: assert property (
        @($global_clock) ($stable(A) && $stable(C) && $stable(D) && $stable(E) && (B != $past(B))) |-> (F == $past(F))
    );

    // Pure combinational behavior: if all inputs are stable, F must remain stable.
    check_stable_inputs_hold_F: assert property (
        @($global_clock) ((A == $past(A)) && (B == $past(B)) && (C == $past(C)) && (D == $past(D)) && (E == $past(E))) |-> (F == $past(F))
    );

    // For A=0, changes on D or E do not affect F when C (and B) are unchanged.
    check_a0_d_or_e_change_no_effect: assert property (
        @($global_clock) (A == 1'b0 && $stable(B) && $stable(C) && ((D != $past(D)) || (E != $past(E)))) |-> (F == $past(F))
    );

    // For A=1 and E=1, if either C or D is 1 then F must be 0.
    check_a1_e1_zero_if_C_or_D_one: assert property (
        @($global_clock) (A == 1'b1 && E == 1'b1 && (C || D)) |-> (F == 1'b0)
    );

    // For A=1 and E=1 with C=0 and D=0, F must be 1.
    check_a1_e1_one_if_C0_D0: assert property (
        @($global_clock) (A == 1'b1 && E == 1'b1 && (C == 1'b0) && (D == 1'b0)) |-> (F == 1'b1)
    );

    // For A=1 and E=0 with C=0 and D=0, F must be 0.
    check_a1_e0_zero_if_C0_D0: assert property (
        @($global_clock) (A == 1'b1 && E == 1'b0 && (C == 1'b0) && (D == 1'b0)) |-> (F == 1'b0)
    );

    // For A=1 and E=0, if C=1 or D=1 then F must be 1.
    check_a1_e0_one_if_C_or_D_one: assert property (
        @($global_clock) (A == 1'b1 && E == 1'b0 && (C || D)) |-> (F == 1'b1)
    );

endmodule