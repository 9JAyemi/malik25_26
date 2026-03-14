module my_module_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1,
    input logic D1,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);
    // No clock or reset in RTL; combinational; assertions use $global_clock.

    // Y equals (A1&A2&B1&C1) OR (!A1&!A2&!B1&!C1).
    check_function_equation: assert property (
        @(posedge $global_clock) Y == ((A1 && A2 && B1 && C1) || ((!A1) && (!A2) && (!B1) && (!C1)))
    );

    // If either input pair mismatches, Y must be 0.
    check_y_zero_on_pair_mismatch: assert property (
        @(posedge $global_clock) ((A1 ^ A2) || (B1 ^ C1)) |-> (Y == 1'b0)
    );

    // When all four controlling inputs are 1, Y must be 1.
    check_y_high_when_all_ones: assert property (
        @(posedge $global_clock) (A1 && A2 && B1 && C1) |-> (Y == 1'b1)
    );

    // When all four controlling inputs are 0, Y must be 1.
    check_y_high_when_all_zeros: assert property (
        @(posedge $global_clock) ((!A1) && (!A2) && (!B1) && (!C1)) |-> (Y == 1'b1)
    );

    // If Y is 1 then both pairs must be equal (no mismatches).
    check_y_implies_equal_pairs: assert property (
        @(posedge $global_clock) (Y == 1'b1) |-> ((A1 == A2) && (B1 == C1))
    );

    // If key inputs are stable across a cycle, Y must be stable.
    check_y_stable_when_key_inputs_stable: assert property (
        @(posedge $global_clock) $stable({A1,A2,B1,C1}) |-> $stable(Y)
    );

    // Changing only D1 must not affect Y.
    check_y_independent_of_d1: assert property (
        @(posedge $global_clock) $changed(D1) && $stable({A1,A2,B1,C1,VPWR,VGND,VPB,VNB}) |-> $stable(Y)
    );

    // Y can change only if at least one key input changes.
    check_y_change_requires_key_change: assert property (
        @(posedge $global_clock) $changed(Y) |-> !$stable({A1,A2,B1,C1})
    );

    // If A-pair is 1s and B-pair is 0s, Y must be 0.
    check_y_zero_when_Apair_ones_Bpair_zeros: assert property (
        @(posedge $global_clock) (A1 && A2 && (!B1) && (!C1)) |-> (Y == 1'b0)
    );

    // If A-pair is 0s and B-pair is 1s, Y must be 0.
    check_y_zero_when_Apair_zeros_Bpair_ones: assert property (
        @(posedge $global_clock) ((!A1) && (!A2) && B1 && C1) |-> (Y == 1'b0)
    );

    // When both pairs are equal, Y equals XNOR of A1 and B1.
    check_y_xnor_when_pairs_equal: assert property (
        @(posedge $global_clock) ((A1 == A2) && (B1 == C1)) |-> (Y == ((A1 && B1) || ((!A1) && (!B1))))
    );

endmodule