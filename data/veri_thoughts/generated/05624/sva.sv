module and_gate_assertions (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic A4,
    input logic B1
);

    // Combinational RTL with no explicit clock or reset; sample on $global_clock.

    // Y must always equal the AND of all five inputs.
    check_and_function: assert property (
        @($global_clock) disable iff ($initstate)
        Y == (A1 && A2 && A3 && A4 && B1)
    );

    // All inputs high forces Y high.
    check_all_inputs_high_implies_y_high: assert property (
        @($global_clock) disable iff ($initstate)
        (A1 && A2 && A3 && A4 && B1) |-> Y
    );

    // Any low input forces Y low.
    check_any_input_low_implies_y_low: assert property (
        @($global_clock) disable iff ($initstate)
        (!A1 || !A2 || !A3 || !A4 || !B1) |-> !Y
    );

    // Y high implies every input is high.
    check_y_high_implies_all_inputs_high: assert property (
        @($global_clock) disable iff ($initstate)
        Y |-> (A1 && A2 && A3 && A4 && B1)
    );

    // If inputs do not change, Y must remain stable.
    check_stable_inputs_hold_y: assert property (
        @($global_clock) disable iff ($initstate)
        ($stable(A1) && $stable(A2) && $stable(A3) && $stable(A4) && $stable(B1)) |-> $stable(Y)
    );

    // Y can only change when at least one input changes.
    check_y_change_requires_input_change: assert property (
        @($global_clock) disable iff ($initstate)
        $changed(Y) |-> ($changed(A1) || $changed(A2) || $changed(A3) || $changed(A4) || $changed(B1))
    );

endmodule