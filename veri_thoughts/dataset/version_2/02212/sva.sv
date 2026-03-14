module sky130_fd_sc_ls__nand4b_sva (
    input logic CLK,
    input logic Y,
    input logic A_N,
    input logic B,
    input logic C,
    input logic D
);
    // Functional equivalence to NAND4 with inverted A_N.
    check_func_nand4b: assert property (
        @(posedge CLK) Y == ~(D & C & B & ~A_N)
    );

    // Equivalent OR-of-literals form.
    check_func_or_form: assert property (
        @(posedge CLK) Y == (A_N | ~B | ~C | ~D)
    );

    // A_N high forces Y high.
    check_an_high_forces_y_high: assert property (
        @(posedge CLK) A_N |-> (Y == 1'b1)
    );

    // B low forces Y high.
    check_b_low_forces_y_high: assert property (
        @(posedge CLK) (B == 1'b0) |-> (Y == 1'b1)
    );

    // C low forces Y high.
    check_c_low_forces_y_high: assert property (
        @(posedge CLK) (C == 1'b0) |-> (Y == 1'b1)
    );

    // D low forces Y high.
    check_d_low_forces_y_high: assert property (
        @(posedge CLK) (D == 1'b0) |-> (Y == 1'b1)
    );

    // Y low only when A_N low and B,C,D high.
    check_y_low_only_when_all_ones: assert property (
        @(posedge CLK) (Y == 1'b0) |-> (A_N == 1'b0 && B == 1'b1 && C == 1'b1 && D == 1'b1)
    );

    // Y changes only when at least one input changes.
    check_y_changes_only_when_inputs_change: assert property (
        @(posedge CLK) $changed(Y) |-> $changed({A_N,B,C,D})
    );

    // If inputs are stable, Y remains stable.
    check_y_stable_when_inputs_stable: assert property (
        @(posedge CLK) $stable({A_N,B,C,D}) |-> $stable(Y)
    );

    // Rising A_N forces Y high.
    check_an_rise_forces_y_high: assert property (
        @(posedge CLK) $rose(A_N) |-> (Y == 1'b1)
    );

    // Falling B forces Y high.
    check_b_fall_forces_y_high: assert property (
        @(posedge CLK) $fell(B) |-> (Y == 1'b1)
    );

    // Falling C forces Y high.
    check_c_fall_forces_y_high: assert property (
        @(posedge CLK) $fell(C) |-> (Y == 1'b1)
    );

    // Falling D forces Y high.
    check_d_fall_forces_y_high: assert property (
        @(posedge CLK) $fell(D) |-> (Y == 1'b1)
    );

    // Falling A_N with B,C,D high forces Y low.
    check_an_fall_with_others_one_forces_y_low: assert property (
        @(posedge CLK) ($fell(A_N) && B && C && D) |-> (Y == 1'b0)
    );

    // Rising B with A_N low and C,D high forces Y low.
    check_b_rise_with_others_one_forces_y_low: assert property (
        @(posedge CLK) ($rose(B) && (A_N == 1'b0) && C && D) |-> (Y == 1'b0)
    );

    // Rising C with A_N low and B,D high forces Y low.
    check_c_rise_with_others_one_forces_y_low: assert property (
        @(posedge CLK) ($rose(C) && (A_N == 1'b0) && B && D) |-> (Y == 1'b0)
    );

    // Rising D with A_N low and B,C high forces Y low.
    check_d_rise_with_others_one_forces_y_low: assert property (
        @(posedge CLK) ($rose(D) && (A_N == 1'b0) && B && C) |-> (Y == 1'b0)
    );
endmodule