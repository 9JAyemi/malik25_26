module mux8_sva (
    input logic [7:0] A,
    input logic [7:0] B,
    input logic       S,
    input logic [7:0] MO
);
    // Event: sample on any edge of S, A, or B.
    clocking cb @(
        posedge S or negedge S
        or posedge A[0] or negedge A[0]
        or posedge A[1] or negedge A[1]
        or posedge A[2] or negedge A[2]
        or posedge A[3] or negedge A[3]
        or posedge A[4] or negedge A[4]
        or posedge A[5] or negedge A[5]
        or posedge A[6] or negedge A[6]
        or posedge A[7] or negedge A[7]
        or posedge B[0] or negedge B[0]
        or posedge B[1] or negedge B[1]
        or posedge B[2] or negedge B[2]
        or posedge B[3] or negedge B[3]
        or posedge B[4] or negedge B[4]
        or posedge B[5] or negedge B[5]
        or posedge B[6] or negedge B[6]
        or posedge B[7] or negedge B[7]
    );
    endclocking
    default clocking cb;

    // Output equals selected input on any input edge.
    check_mux_function: assert property (
        MO == (S ? B : A)
    );

    // When S=0 and only B changes, MO stays driven by A (no change).
    check_unselected_b_no_effect_s0: assert property (
        (S == 1'b0) && $changed(B) && $stable(A) && $stable(S) |-> $stable(MO) && (MO == A)
    );

    // When S=1 and only A changes, MO stays driven by B (no change).
    check_unselected_a_no_effect_s1: assert property (
        (S == 1'b1) && $changed(A) && $stable(B) && $stable(S) |-> $stable(MO) && (MO == B)
    );

    // When S=0 and A changes (S stable), MO follows A.
    check_selected_a_updates_output_s0: assert property (
        (S == 1'b0) && $changed(A) && $stable(S) |-> (MO == A)
    );

    // When S=1 and B changes (S stable), MO follows B.
    check_selected_b_updates_output_s1: assert property (
        (S == 1'b1) && $changed(B) && $stable(S) |-> (MO == B)
    );

    // If A, B, and S are all stable, MO must be stable.
    check_output_stable_when_inputs_stable: assert property (
        $stable(A) && $stable(B) && $stable(S) |-> $stable(MO)
    );

    // On S rising with A and B stable, MO equals B.
    check_s_rise_selects_b: assert property (
        $rose(S) && $stable(A) && $stable(B) |-> (MO == B)
    );

    // On S falling with A and B stable, MO equals A.
    check_s_fall_selects_a: assert property (
        $fell(S) && $stable(A) && $stable(B) |-> (MO == A)
    );

    // On S rising with A!=B and A/B stable, MO must change.
    check_s_rise_changes_output_if_inputs_differ: assert property (
        $rose(S) && $stable(A) && $stable(B) && (A != B) |-> $changed(MO)
    );

    // On S falling with A!=B and A/B stable, MO must change.
    check_s_fall_changes_output_if_inputs_differ: assert property (
        $fell(S) && $stable(A) && $stable(B) && (A != B) |-> $changed(MO)
    );
endmodule