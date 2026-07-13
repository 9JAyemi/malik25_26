module mux_4to1_sva (
    input logic clk,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1,
    input logic Y
);
    // Y implements a 2:1 mux selecting B1 when C1=1 else A2.
    check_y_mux_function: assert property (
        @(posedge clk) Y == (C1 ? B1 : A2)
    );

    // Changing A1 alone does not affect Y.
    check_y_independent_of_A1: assert property (
        @(posedge clk) ($changed(A1) && $stable(B1) && $stable(B2) && $stable(C1) && $stable(A2)) |-> $stable(Y)
    );

    // Changing B2 alone does not affect Y.
    check_y_independent_of_B2: assert property (
        @(posedge clk) ($changed(B2) && $stable(B1) && $stable(A1) && $stable(C1) && $stable(A2)) |-> $stable(Y)
    );

    // With C1=1 and others stable, changing A2 does not affect Y.
    check_y_independent_of_A2_when_C1: assert property (
        @(posedge clk) (C1 && $stable(C1) && $changed(A2) && $stable(B1) && $stable(B2) && $stable(A1)) |-> $stable(Y)
    );

    // With C1=0 and others stable, changing B1 does not affect Y.
    check_y_independent_of_B1_when_not_C1: assert property (
        @(posedge clk) (!C1 && $stable(C1) && $changed(B1) && $stable(A1) && $stable(B2) && $stable(A2)) |-> $stable(Y)
    );

    // With C1=1 and others stable, Y follows B1 changes.
    check_y_tracks_B1_when_C1: assert property (
        @(posedge clk) (C1 && $stable(C1) && $changed(B1) && $stable(A1) && $stable(A2) && $stable(B2)) |-> $changed(Y)
    );

    // With C1=0 and others stable, Y follows A2 changes.
    check_y_tracks_A2_when_not_C1: assert property (
        @(posedge clk) (!C1 && $stable(C1) && $changed(A2) && $stable(A1) && $stable(B1) && $stable(B2)) |-> $changed(Y)
    );

    // If only C1 toggles and B1 != A2, Y must change.
    check_y_c1_toggle_changes_when_b1_ne_a2: assert property (
        @(posedge clk) ($changed(C1) && $stable(A1) && $stable(A2) && $stable(B1) && $stable(B2) && (B1 != A2)) |-> $changed(Y)
    );

    // If only C1 toggles and B1 == A2, Y must remain stable.
    check_y_c1_toggle_nochange_when_b1_eq_a2: assert property (
        @(posedge clk) ($changed(C1) && $stable(A1) && $stable(A2) && $stable(B1) && $stable(B2) && (B1 == A2)) |-> $stable(Y)
    );
endmodule