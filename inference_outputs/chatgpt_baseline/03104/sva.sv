module OR3_gate_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic X,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // X must equal the OR of the three logic inputs.
    check_or_function: assert property (
        @(posedge clk) X == (A | B | C)
    );

    // X LOW means all three logic inputs are LOW.
    check_x_low_implies_all_inputs_low: assert property (
        @(posedge clk) !X |-> (!A && !B && !C)
    );

    // All three logic inputs LOW must drive X LOW.
    check_all_inputs_low_drive_x_low: assert property (
        @(posedge clk) (!A && !B && !C) |-> !X
    );

    // A HIGH must drive X HIGH.
    check_a_high_drives_x_high: assert property (
        @(posedge clk) A |-> X
    );

    // B HIGH must drive X HIGH.
    check_b_high_drives_x_high: assert property (
        @(posedge clk) B |-> X
    );

    // C HIGH must drive X HIGH.
    check_c_high_drives_x_high: assert property (
        @(posedge clk) C |-> X
    );

    // Stable logic inputs must keep X stable.
    check_stable_inputs_keep_x_stable: assert property (
        @(posedge clk) $stable({A, B, C}) |-> $stable(X)
    );

    // A sampled change on X requires a sampled change on a logic input.
    check_x_change_requires_logic_input_change: assert property (
        @(posedge clk) !$stable(X) |-> !$stable({A, B, C})
    );

    // Power-pin changes alone must not affect X.
    check_power_pin_changes_do_not_affect_x: assert property (
        @(posedge clk) $stable({A, B, C}) && !$stable({VPWR, VGND, VPB, VNB}) |-> $stable(X)
    );

endmodule