module sky130_fd_sc_lp__o311a_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic C1
);
    // DUT has no clock/reset; combinational. Sample on clk; no reset gating (disable iff 1'b0). X = (A1|A2|A3)&B1&C1.

    // X implements the exact Boolean equation.
    check_function_equivalence: assert property (
        @(posedge clk) disable iff (1'b0) X == ((A1 | A2 | A3) & B1 & C1)
    );

    // B1 low forces X low.
    check_b1_low_forces_x0: assert property (
        @(posedge clk) disable iff (1'b0) (!B1) |-> (!X)
    );

    // C1 low forces X low.
    check_c1_low_forces_x0: assert property (
        @(posedge clk) disable iff (1'b0) (!C1) |-> (!X)
    );

    // All A inputs low force X low.
    check_all_a_low_forces_x0: assert property (
        @(posedge clk) disable iff (1'b0) (!A1 && !A2 && !A3) |-> (!X)
    );

    // B1 and C1 high with any A high drives X high.
    check_gate_true_drives_x1: assert property (
        @(posedge clk) disable iff (1'b0) (B1 && C1 && (A1 || A2 || A3)) |-> X
    );

    // X high implies B1 and C1 high and at least one A high.
    check_x_high_implies_inputs: assert property (
        @(posedge clk) disable iff (1'b0) X |-> (B1 && C1 && (A1 || A2 || A3))
    );

    // Rising X requires B1 and C1 high and at least one A high.
    check_x_rise_requires_conditions: assert property (
        @(posedge clk) disable iff (1'b0) $rose(X) |-> (B1 && C1 && (A1 || A2 || A3))
    );

    // Falling X implies some required input condition is false.
    check_x_fall_implies_blocking_input: assert property (
        @(posedge clk) disable iff (1'b0) $fell(X) |-> ((!B1) || (!C1) || (!A1 && !A2 && !A3))
    );

    // If all inputs are stable across a cycle, X must be stable.
    check_stable_inputs_hold_output: assert property (
        @(posedge clk) disable iff (1'b0) ($stable(A1) && $stable(A2) && $stable(A3) && $stable(B1) && $stable(C1)) |-> $stable(X)
    );
endmodule