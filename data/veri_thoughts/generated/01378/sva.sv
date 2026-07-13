module mux_4_1_sva (
    // Analysis: no clock/reset in RTL; pure combinational 4:1 mux built from 2:1; Y = S1 ? (S0?D:C) : (S0?B:A)
    input logic clk,   // sampling clock for assertions
    input logic Y,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic S0,
    input logic S1
);
    // Y matches the composed 4:1 mux function.
    check_functional_equivalence: assert property (
        @(posedge clk) Y == (S1 ? (S0 ? D : C) : (S0 ? B : A))
    );

    // When S1=0,S0=0, Y selects A.
    check_select_00_selects_A: assert property (
        @(posedge clk) (!S1 && !S0) |-> (Y == A)
    );

    // When S1=0,S0=1, Y selects B.
    check_select_01_selects_B: assert property (
        @(posedge clk) (!S1 && S0) |-> (Y == B)
    );

    // When S1=1,S0=0, Y selects C.
    check_select_10_selects_C: assert property (
        @(posedge clk) (S1 && !S0) |-> (Y == C)
    );

    // When S1=1,S0=1, Y selects D.
    check_select_11_selects_D: assert property (
        @(posedge clk) (S1 && S0) |-> (Y == D)
    );

    // If all inputs and selects are stable, Y must be stable.
    check_output_stable_when_inputs_stable: assert property (
        @(posedge clk) $stable(A) && $stable(B) && $stable(C) && $stable(D) && $stable(S0) && $stable(S1) |-> $stable(Y)
    );

    // If Y changes, at least one input or select must have changed.
    check_output_change_has_cause: assert property (
        @(posedge clk) $changed(Y) |-> ($changed(A) || $changed(B) || $changed(C) || $changed(D) || $changed(S0) || $changed(S1))
    );

    // If S1 toggles while others are stable and selected paths differ, Y must change.
    check_y_changes_on_S1_toggle_when_paths_differ: assert property (
        @(posedge clk)
            $changed(S1) && $stable(S0) && $stable(A) && $stable(B) && $stable(C) && $stable(D) &&
            ((S0 ? B : A) != (S0 ? D : C))
            |-> $changed(Y)
    );

    // If S0 toggles with S1=0 and A!=B (others stable), Y must change.
    check_y_changes_on_S0_toggle_S1_0: assert property (
        @(posedge clk)
            !S1 && $stable(S1) && $changed(S0) && $stable(A) && $stable(B) && (A != B)
            |-> $changed(Y)
    );

    // If S0 toggles with S1=1 and C!=D (others stable), Y must change.
    check_y_changes_on_S0_toggle_S1_1: assert property (
        @(posedge clk)
            S1 && $stable(S1) && $changed(S0) && $stable(C) && $stable(D) && (C != D)
            |-> $changed(Y)
    );
endmodule