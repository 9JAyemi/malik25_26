module xnor4_sva (
    input logic CLK,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic X
);
    // X equals 4-input XNOR of A,B,C,D.
    check_x_equiv_xnor4: assert property (
        @(posedge CLK) X == ~(A ^ B ^ C ^ D)
    );

    // X equals XNOR of pairwise XNORs (A~^B) and (C~^D).
    check_x_equiv_pair_ab_cd: assert property (
        @(posedge CLK) X == ((A ~^ B) ~^ (C ~^ D))
    );

    // X equals XNOR of pairwise XNORs (A~^C) and (B~^D).
    check_x_equiv_pair_ac_bd: assert property (
        @(posedge CLK) X == ((A ~^ C) ~^ (B ~^ D))
    );

    // X equals XNOR of pairwise XNORs (A~^D) and (B~^C).
    check_x_equiv_pair_ad_bc: assert property (
        @(posedge CLK) X == ((A ~^ D) ~^ (B ~^ C))
    );

    // Output change parity equals XOR of input change parities.
    check_change_parity_matches_inputs: assert property (
        @(posedge CLK) $changed(X) == ($changed(A) ^ $changed(B) ^ $changed(C) ^ $changed(D))
    );

    // If inputs are stable between cycles, X is stable.
    check_stable_when_inputs_stable: assert property (
        @(posedge CLK) $stable({A,B,C,D}) |-> $stable(X)
    );

    // If exactly one input toggles, X toggles.
    check_single_input_toggle_changes_x: assert property (
        @(posedge CLK) (($changed(A)+$changed(B)+$changed(C)+$changed(D)) == 1) |-> $changed(X)
    );

    // If exactly two inputs toggle, X remains stable.
    check_two_input_toggle_keeps_x: assert property (
        @(posedge CLK) (($changed(A)+$changed(B)+$changed(C)+$changed(D)) == 2) |-> !$changed(X)
    );

    // If exactly three inputs toggle, X toggles.
    check_three_input_toggle_changes_x: assert property (
        @(posedge CLK) (($changed(A)+$changed(B)+$changed(C)+$changed(D)) == 3) |-> $changed(X)
    );

    // If all four inputs toggle, X remains stable.
    check_four_input_toggle_keeps_x: assert property (
        @(posedge CLK) (($changed(A)+$changed(B)+$changed(C)+$changed(D)) == 4) |-> !$changed(X)
    );
endmodule