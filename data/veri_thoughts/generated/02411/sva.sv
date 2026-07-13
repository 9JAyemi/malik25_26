module sky130_fd_sc_hd__or3b_sva (
    input logic clk,  // sampling clock (DUT has no clock)
    input logic X,
    input logic A,
    input logic B,
    input logic C_N
);
    // Analysis: no clock/reset in DUT; pure combinational 3-input OR with inverted C_N (X = A | B | ~C_N).

    // X must implement X = A | B | ~C_N.
    check_function_equivalence: assert property (
        @(posedge clk) X == (A || B || !C_N)
    );

    // A high forces X high.
    check_a_forces_x_high: assert property (
        @(posedge clk) A |-> (X == 1'b1)
    );

    // B high forces X high.
    check_b_forces_x_high: assert property (
        @(posedge clk) B |-> (X == 1'b1)
    );

    // C_N low (active-low input) forces X high.
    check_cn_low_forces_x_high: assert property (
        @(posedge clk) (!C_N) |-> (X == 1'b1)
    );

    // All inputs deasserted (A=0,B=0,C_N=1) force X low.
    check_blocking_inputs_force_x_low: assert property (
        @(posedge clk) (!A && !B && C_N) |-> (X == 1'b0)
    );

    // X low implies A=0, B=0, and C_N=1.
    check_x_low_implies_inputs_blocking: assert property (
        @(posedge clk) (X == 1'b0) |-> (!A && !B && C_N)
    );

    // X high implies A=1 or B=1 or C_N=0.
    check_x_high_implies_some_input_asserted: assert property (
        @(posedge clk) (X == 1'b1) |-> (A || B || !C_N)
    );

    // If A,B,C_N are stable, X must be stable (no state/memory).
    check_stability_when_inputs_stable: assert property (
        @(posedge clk) $stable(A) && $stable(B) && $stable(C_N) |-> $stable(X)
    );

    // Rising A drives X high immediately.
    check_a_rise_drives_x_high: assert property (
        @(posedge clk) $rose(A) |-> (X == 1'b1)
    );

    // Rising B drives X high immediately.
    check_b_rise_drives_x_high: assert property (
        @(posedge clk) $rose(B) |-> (X == 1'b1)
    );

    // Falling C_N (i.e., C_N=1->0) drives X high immediately.
    check_cn_fall_drives_x_high: assert property (
        @(posedge clk) $fell(C_N) |-> (X == 1'b1)
    );

    // Falling A with B=0 and C_N=1 drives X low.
    check_a_fall_with_others_low_drives_x_low: assert property (
        @(posedge clk) $fell(A) && (B == 1'b0) && (C_N == 1'b1) |-> (X == 1'b0)
    );

    // Falling B with A=0 and C_N=1 drives X low.
    check_b_fall_with_others_low_drives_x_low: assert property (
        @(posedge clk) $fell(B) && (A == 1'b0) && (C_N == 1'b1) |-> (X == 1'b0)
    );

    // Rising C_N with A=0 and B=0 drives X low.
    check_cn_rise_with_others_low_drives_x_low: assert property (
        @(posedge clk) $rose(C_N) && (A == 1'b0) && (B == 1'b0) |-> (X == 1'b0)
    );
endmodule