module sky130_fd_sc_ls__and3_sva (
    input logic CLK,
    input logic X,
    input logic A,
    input logic B,
    input logic C
);
    // Output equals logical AND of inputs.
    check_functional_and: assert property (
        @(posedge CLK) disable iff (1'b0) X == (A & B & C)
    );

    // X HIGH implies all inputs HIGH.
    check_x_high_implies_inputs_high: assert property (
        @(posedge CLK) disable iff (1'b0) X |-> (A && B && C)
    );

    // All inputs HIGH implies X HIGH.
    check_all_inputs_high_implies_x_high: assert property (
        @(posedge CLK) disable iff (1'b0) (A && B && C) |-> X
    );

    // !A forces X LOW.
    check_low_a_forces_x_low: assert property (
        @(posedge CLK) disable iff (1'b0) (!A) |-> (!X)
    );

    // !B forces X LOW.
    check_low_b_forces_x_low: assert property (
        @(posedge CLK) disable iff (1'b0) (!B) |-> (!X)
    );

    // !C forces X LOW.
    check_low_c_forces_x_low: assert property (
        @(posedge CLK) disable iff (1'b0) (!C) |-> (!X)
    );

    // With B&C HIGH, X equals A.
    check_bc_high_gates_a_to_x: assert property (
        @(posedge CLK) disable iff (1'b0) (B && C) |-> (X == A)
    );

    // With A&C HIGH, X equals B.
    check_ac_high_gates_b_to_x: assert property (
        @(posedge CLK) disable iff (1'b0) (A && C) |-> (X == B)
    );

    // With A&B HIGH, X equals C.
    check_ab_high_gates_c_to_x: assert property (
        @(posedge CLK) disable iff (1'b0) (A && B) |-> (X == C)
    );

    // X can only rise if at least one input rises.
    check_x_rise_requires_input_rise: assert property (
        @(posedge CLK) disable iff (1'b0) $rose(X) |-> ($rose(A) || $rose(B) || $rose(C))
    );

    // X can only fall if at least one input falls.
    check_x_fall_requires_input_fall: assert property (
        @(posedge CLK) disable iff (1'b0) $fell(X) |-> ($fell(A) || $fell(B) || $fell(C))
    );

    // If all inputs are stable, X is stable.
    check_stable_inputs_imply_stable_x: assert property (
        @(posedge CLK) disable iff (1'b0) ($stable(A) && $stable(B) && $stable(C)) |-> $stable(X)
    );
endmodule