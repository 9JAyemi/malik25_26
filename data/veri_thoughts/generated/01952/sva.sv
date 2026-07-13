module sky130_fd_sc_hdll__xor3_sva (
    input logic X,
    input logic A,
    input logic B,
    input logic C
);
    // X equals A^B^C when sampled on A's rising edge.
    check_x_eq_parity_on_A: assert property (
        @(posedge A) X == (A ^ B ^ C)
    );

    // X equals A^B^C when sampled on B's rising edge.
    check_x_eq_parity_on_B: assert property (
        @(posedge B) X == (A ^ B ^ C)
    );

    // X equals A^B^C when sampled on C's rising edge.
    check_x_eq_parity_on_C: assert property (
        @(posedge C) X == (A ^ B ^ C)
    );

    // If only A toggles (B,C stable), X must toggle.
    check_single_toggle_A_changes_X: assert property (
        @(posedge A) ($stable(B) && $stable(C)) |-> $changed(X)
    );

    // If only B toggles (A,C stable), X must toggle.
    check_single_toggle_B_changes_X: assert property (
        @(posedge B) ($stable(A) && $stable(C)) |-> $changed(X)
    );

    // If only C toggles (A,B stable), X must toggle.
    check_single_toggle_C_changes_X: assert property (
        @(posedge C) ($stable(A) && $stable(B)) |-> $changed(X)
    );

    // If A and B toggle together (C stable), X must not change.
    check_double_toggle_AB_keeps_X: assert property (
        @(posedge A) ($changed(B) && $stable(C)) |-> !$changed(X)
    );

    // If A and C toggle together (B stable), X must not change.
    check_double_toggle_AC_keeps_X: assert property (
        @(posedge A) ($changed(C) && $stable(B)) |-> !$changed(X)
    );

    // If B and C toggle together (A stable), X must not change.
    check_double_toggle_BC_keeps_X: assert property (
        @(posedge B) ($changed(C) && $stable(A)) |-> !$changed(X)
    );

    // Any change on X must be caused by a change on at least one input.
    check_x_change_requires_input_change: assert property (
        @(posedge A or posedge B or posedge C or posedge X) $changed(X) |-> ($changed(A) || $changed(B) || $changed(C))
    );
endmodule