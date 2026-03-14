module sky130_fd_sc_ms__o211ai_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1
);
    ///// Combinational truth table checks (clocked on $global_clock) /////
    // When B1&C1 and (A1|A2) are HIGH, Y must be LOW (Y = ~(C1 & B1 & (A1|A2))).
    check_y_low_when_all_high: assert property (
        @($global_clock) (B1 && C1 && (A1 || A2)) |-> (Y == 1'b0)
    );
    // Y LOW only if B1&C1 are HIGH and (A1|A2) is HIGH.
    check_y_low_implies_inputs_high: assert property (
        @($global_clock) (Y == 1'b0) |-> (B1 && C1 && (A1 || A2))
    );
    // If B1 is LOW, Y must be HIGH.
    check_b1_low_forces_y_high: assert property (
        @($global_clock) (!B1) |-> (Y == 1'b1)
    );
    // If C1 is LOW, Y must be HIGH.
    check_c1_low_forces_y_high: assert property (
        @($global_clock) (!C1) |-> (Y == 1'b1)
    );
    // If both A1 and A2 are LOW, Y must be HIGH.
    check_both_a_low_force_y_high: assert property (
        @($global_clock) (!A1 && !A2) |-> (Y == 1'b1)
    );
    // If Y is HIGH, at least one of B1, C1 is LOW or both A1 and A2 are LOW.
    check_y_high_implies_some_input_low: assert property (
        @($global_clock) (Y == 1'b1) |-> (!B1 || !C1 || (!A1 && !A2))
    );

    ///// Temporal consistency /////
    // If all inputs are stable, Y must be stable.
    check_output_stable_when_inputs_stable: assert property (
        @($global_clock) $stable({A1, A2, B1, C1}) |-> $stable(Y)
    );

    ///// Edge-based functional responses /////
    // If B1 rises while C1 and (A1|A2) are HIGH in both cycles, Y must fall.
    check_y_fall_on_b1_rise_when_active: assert property (
        @($global_clock) ($rose(B1) && C1 && $past(C1) && (A1 || A2) && ($past(A1) || $past(A2))) |-> $fell(Y)
    );
    // If C1 rises while B1 and (A1|A2) are HIGH in both cycles, Y must fall.
    check_y_fall_on_c1_rise_when_active: assert property (
        @($global_clock) ($rose(C1) && B1 && $past(B1) && (A1 || A2) && ($past(A1) || $past(A2))) |-> $fell(Y)
    );
    // If A1 or A2 rises from 0 while the other is 0 and B1&C1 are HIGH in both cycles, Y must fall.
    check_y_fall_on_or_input_rise_when_gate_high: assert property (
        @($global_clock)
            (
                (
                    $rose(A1) && !$past(A1) && !A2 && !$past(A2)
                ) || (
                    $rose(A2) && !$past(A2) && !A1 && !$past(A1)
                )
            ) && B1 && $past(B1) && C1 && $past(C1)
            |-> $fell(Y)
    );
endmodule