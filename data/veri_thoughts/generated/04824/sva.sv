module logic_gate_sva (
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

    // Y must equal the AND of all logic and power inputs.
    check_output_equivalence: assert property (
        @($global_clock)
        Y == (A1 & A2 & B1 & C1 & D1 & VPWR & VGND & VPB & VNB)
    );

    // Y must be high when every input is high.
    check_all_high_drives_high: assert property (
        @($global_clock)
        (A1 && A2 && B1 && C1 && D1 && VPWR && VGND && VPB && VNB) |-> Y
    );

    // A high Y requires every input to be high.
    check_output_high_requires_all_high: assert property (
        @($global_clock)
        Y |-> (A1 && A2 && B1 && C1 && D1 && VPWR && VGND && VPB && VNB)
    );

    // Any low input must force Y low.
    check_any_low_drives_low: assert property (
        @($global_clock)
        !(A1 && A2 && B1 && C1 && D1 && VPWR && VGND && VPB && VNB) |-> !Y
    );

    // With power pins high, Y reduces to the AND of the logic inputs.
    check_logic_inputs_control_when_power_high: assert property (
        @($global_clock)
        (VPWR && VGND && VPB && VNB) |-> (Y == (A1 & A2 & B1 & C1 & D1))
    );

    // With logic inputs high, Y reduces to the AND of the power pins.
    check_power_pins_control_when_logic_high: assert property (
        @($global_clock)
        (A1 && A2 && B1 && C1 && D1) |-> (Y == (VPWR & VGND & VPB & VNB))
    );

    // If all inputs are stable, Y must remain stable.
    check_stable_inputs_hold_output: assert property (
        @($global_clock)
        ($stable(A1) && $stable(A2) && $stable(B1) && $stable(C1) && $stable(D1) &&
         $stable(VPWR) && $stable(VGND) && $stable(VPB) && $stable(VNB)) |-> $stable(Y)
    );

    // Y can only change if at least one input changes.
    check_output_change_requires_input_change: assert property (
        @($global_clock)
        $changed(Y) |-> ($changed(A1) || $changed(A2) || $changed(B1) || $changed(C1) ||
                         $changed(D1) || $changed(VPWR) || $changed(VGND) ||
                         $changed(VPB) || $changed(VNB))
    );

endmodule