module sky130_fd_sc_hd__o2111ai_sva (
    input logic CLK,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1,
    input logic D1
);
    // Y matches combinational function when inputs known.
    check_functional_equivalence: assert property (
        @(posedge CLK) (! $isunknown({A1,A2,B1,C1,D1})) |-> ( Y == ~( (A1 | A2) & ~(B1 & C1 & D1) ) )
    );

    // Y is 1 when B1,C1,D1 are all 1.
    y_one_when_bcd_all_high: assert property (
        @(posedge CLK) (B1 & C1 & D1) |-> (Y == 1'b1)
    );

    // Y is 1 when (A1|A2) is 0.
    y_one_when_A_or_is_zero: assert property (
        @(posedge CLK) ~(A1 | A2) |-> (Y == 1'b1)
    );

    // If (A1|A2)=1 and not all of B1,C1,D1 are 1, Y is 0.
    y_zero_when_A_or_and_not_all_bcd: assert property (
        @(posedge CLK) ((A1 | A2) && !(B1 && C1 && D1)) |-> (Y == 1'b0)
    );

    // Y==0 implies (A1|A2)=1 and not all of B1,C1,D1 are 1.
    y_zero_implies_A_or_and_not_bcd_all: assert property (
        @(posedge CLK) (Y == 1'b0) |-> ((A1 | A2) && !(B1 && C1 && D1))
    );

    // Y==1 implies either (A1|A2)=0 or (B1&C1&D1)=1.
    y_one_implies_norA_or_bcd_all: assert property (
        @(posedge CLK) (Y == 1'b1) |-> ( ~(A1 | A2) || (B1 && C1 && D1) )
    );

    // Output changes only if at least one input changes.
    y_change_implies_input_change: assert property (
        @(posedge CLK) $changed(Y) |-> ($changed(A1) || $changed(A2) || $changed(B1) || $changed(C1) || $changed(D1))
    );

    // If all inputs are stable across a cycle, Y is stable.
    y_stable_when_inputs_stable: assert property (
        @(posedge CLK) ($stable(A1) && $stable(A2) && $stable(B1) && $stable(C1) && $stable(D1)) |-> $stable(Y)
    );

    // If inputs are known (no X/Z), Y must be known.
    y_known_when_inputs_known: assert property (
        @(posedge CLK) (! $isunknown({A1,A2,B1,C1,D1})) |-> (! $isunknown(Y))
    );

    // Swapping A1 and A2 while B1,C1,D1 are stable leaves Y unchanged.
    y_invariant_under_A_swap: assert property (
        @(posedge CLK) ($stable(B1) && $stable(C1) && $stable(D1) && (A1 == $past(A2)) && (A2 == $past(A1))) |-> (Y == $past(Y))
    );
endmodule