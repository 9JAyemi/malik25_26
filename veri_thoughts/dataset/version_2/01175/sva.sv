module and4_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic Y
);
    // Pure combinational AND of A,B,C,D to Y; sample on $global_clock.

    // When all signals are known, Y equals A&B&C&D.
    check_y_functional_when_known: assert property (
        @(posedge $global_clock) (!$isunknown({A,B,C,D,Y})) |-> (Y == (A & B & C & D))
    );

    // If Y is HIGH, then all inputs are HIGH.
    check_y_high_implies_inputs_high: assert property (
        @(posedge $global_clock) (Y == 1'b1) |-> (A && B && C && D)
    );

    // If all inputs are HIGH, Y is HIGH.
    check_inputs_high_implies_y_high: assert property (
        @(posedge $global_clock) (A && B && C && D) |-> (Y == 1'b1)
    );

    // A LOW forces Y LOW.
    check_zero_dominance_A: assert property (
        @(posedge $global_clock) (A == 1'b0) |-> (Y == 1'b0)
    );

    // B LOW forces Y LOW.
    check_zero_dominance_B: assert property (
        @(posedge $global_clock) (B == 1'b0) |-> (Y == 1'b0)
    );

    // C LOW forces Y LOW.
    check_zero_dominance_C: assert property (
        @(posedge $global_clock) (C == 1'b0) |-> (Y == 1'b0)
    );

    // D LOW forces Y LOW.
    check_zero_dominance_D: assert property (
        @(posedge $global_clock) (D == 1'b0) |-> (Y == 1'b0)
    );

    // Y only changes when at least one input changes.
    check_y_changes_only_on_input_change: assert property (
        @(posedge $global_clock) $changed(Y) |-> ($changed(A) || $changed(B) || $changed(C) || $changed(D))
    );

    // Y rising edge implies all inputs are HIGH.
    check_y_rise_requires_all_ones: assert property (
        @(posedge $global_clock) $rose(Y) |-> (A && B && C && D)
    );

    // Y falling edge implies at least one input is LOW.
    check_y_fall_requires_any_zero: assert property (
        @(posedge $global_clock) $fell(Y) |-> (!A || !B || !C || !D)
    );
endmodule