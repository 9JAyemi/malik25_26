module four_input_and_gate_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // No explicit clock or reset in the RTL; use $global_clock for this combinational module.

    // Y must always match the implemented three-input AND function.
    check_y_matches_and_function: assert property (
        @($global_clock) (Y === (A1 & A2 & B1))
    );

    // All three logic inputs high must drive Y high.
    check_all_inputs_high_drive_y_high: assert property (
        @($global_clock)
        ((A1 === 1'b1) && (A2 === 1'b1) && (B1 === 1'b1)) |-> (Y === 1'b1)
    );

    // A1 low must force Y low.
    check_a1_low_forces_y_low: assert property (
        @($global_clock) (A1 === 1'b0) |-> (Y === 1'b0)
    );

    // A2 low must force Y low.
    check_a2_low_forces_y_low: assert property (
        @($global_clock) (A2 === 1'b0) |-> (Y === 1'b0)
    );

    // B1 low must force Y low.
    check_b1_low_forces_y_low: assert property (
        @($global_clock) (B1 === 1'b0) |-> (Y === 1'b0)
    );

    // A high Y requires A1 to be high.
    check_y_high_requires_a1_high: assert property (
        @($global_clock) (Y === 1'b1) |-> (A1 === 1'b1)
    );

    // A high Y requires A2 to be high.
    check_y_high_requires_a2_high: assert property (
        @($global_clock) (Y === 1'b1) |-> (A2 === 1'b1)
    );

    // A high Y requires B1 to be high.
    check_y_high_requires_b1_high: assert property (
        @($global_clock) (Y === 1'b1) |-> (B1 === 1'b1)
    );

    // If A1, A2, and B1 are stable, Y must remain stable.
    check_y_stable_when_logic_inputs_stable: assert property (
        @($global_clock) ($stable(A1) && $stable(A2) && $stable(B1)) |-> $stable(Y)
    );

    // Changes on unused power pins alone must not affect Y.
    check_power_pin_changes_do_not_affect_y: assert property (
        @($global_clock)
        ($stable(A1) && $stable(A2) && $stable(B1) &&
         (!$stable(VPWR) || !$stable(VGND) || !$stable(VPB) || !$stable(VNB)))
        |-> $stable(Y)
    );

endmodule