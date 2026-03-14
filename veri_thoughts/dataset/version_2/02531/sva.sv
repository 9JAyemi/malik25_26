module my_nand_sva (
    input logic CLK,
    input logic RESETn,
    input logic A,
    input logic B,
    input logic Y
);
    // Y equals A | ~B when all are known.
    check_functional_equivalence_known: assert property (
        @(posedge CLK) disable iff (!RESETn) !$isunknown({A,B,Y}) |-> (Y == (A | ~B))
    );

    // If B is 0, Y must be 1.
    check_B_low_forces_Y_high: assert property (
        @(posedge CLK) disable iff (!RESETn) (B == 1'b0) |-> (Y == 1'b1)
    );

    // If B is 1, Y equals A.
    check_B_high_equals_A: assert property (
        @(posedge CLK) disable iff (!RESETn) (B == 1'b1) |-> (Y == A)
    );

    // If A is 0, Y equals ~B.
    check_A_low_equals_notB: assert property (
        @(posedge CLK) disable iff (!RESETn) (A == 1'b0) |-> (Y == ~B)
    );

    // Y can be 0 only when A==0 and B==1.
    check_only_case_Y_low: assert property (
        @(posedge CLK) disable iff (!RESETn) (Y == 1'b0) |-> ((A == 1'b0) && (B == 1'b1))
    );

    // If Y is 1, then A==1 or B==0.
    check_Y_high_implies_A_or_notB: assert property (
        @(posedge CLK) disable iff (!RESETn) (Y == 1'b1) |-> ((A == 1'b1) || (B == 1'b0))
    );

    // If inputs are stable cycle-to-cycle, output is stable.
    check_stable_if_inputs_stable: assert property (
        @(posedge CLK) disable iff (!RESETn) $stable(A) && $stable(B) |-> $stable(Y)
    );

    // Y changes only if A or B changes.
    check_Y_change_requires_input_change: assert property (
        @(posedge CLK) disable iff (!RESETn) $changed(Y) |-> ($changed(A) || $changed(B))
    );

    // If A and B are known, Y is known.
    check_knownness_when_inputs_known: assert property (
        @(posedge CLK) disable iff (!RESETn) !$isunknown({A,B}) |-> !$isunknown(Y)
    );
endmodule