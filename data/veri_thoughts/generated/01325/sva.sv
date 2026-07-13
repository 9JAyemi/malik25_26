module parity_check_sva (
    input logic CLK,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic parity
);

    // parity equals XOR of all inputs
    check_parity_function: assert property (
        @(posedge CLK) parity == (A ^ B ^ C ^ D)
    );

    // If inputs are stable, parity must be stable
    check_parity_stable_on_inputs_stable: assert property (
        @(posedge CLK) $stable({A,B,C,D}) |-> $stable(parity)
    );

    // If only A changes, parity must change
    check_single_change_A_toggles_parity: assert property (
        @(posedge CLK) $changed(A) && $stable(B) && $stable(C) && $stable(D) |-> $changed(parity)
    );

    // If only B changes, parity must change
    check_single_change_B_toggles_parity: assert property (
        @(posedge CLK) $changed(B) && $stable(A) && $stable(C) && $stable(D) |-> $changed(parity)
    );

    // If only C changes, parity must change
    check_single_change_C_toggles_parity: assert property (
        @(posedge CLK) $changed(C) && $stable(A) && $stable(B) && $stable(D) |-> $changed(parity)
    );

    // If only D changes, parity must change
    check_single_change_D_toggles_parity: assert property (
        @(posedge CLK) $changed(D) && $stable(A) && $stable(B) && $stable(C) |-> $changed(parity)
    );

    // If A and B both change and C,D stable, parity must be unchanged
    check_two_changes_AB_hold_parity: assert property (
        @(posedge CLK) $changed(A) && $changed(B) && $stable(C) && $stable(D) |-> $stable(parity)
    );

    // If A and C both change and B,D stable, parity must be unchanged
    check_two_changes_AC_hold_parity: assert property (
        @(posedge CLK) $changed(A) && $changed(C) && $stable(B) && $stable(D) |-> $stable(parity)
    );

    // If A and D both change and B,C stable, parity must be unchanged
    check_two_changes_AD_hold_parity: assert property (
        @(posedge CLK) $changed(A) && $changed(D) && $stable(B) && $stable(C) |-> $stable(parity)
    );

    // If B and C both change and A,D stable, parity must be unchanged
    check_two_changes_BC_hold_parity: assert property (
        @(posedge CLK) $changed(B) && $changed(C) && $stable(A) && $stable(D) |-> $stable(parity)
    );

    // If B and D both change and A,C stable, parity must be unchanged
    check_two_changes_BD_hold_parity: assert property (
        @(posedge CLK) $changed(B) && $changed(D) && $stable(A) && $stable(C) |-> $stable(parity)
    );

    // If C and D both change and A,B stable, parity must be unchanged
    check_two_changes_CD_hold_parity: assert property (
        @(posedge CLK) $changed(C) && $changed(D) && $stable(A) && $stable(B) |-> $stable(parity)
    );

endmodule