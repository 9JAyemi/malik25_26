module sky130_fd_sc_hdll__and4bb_sva (
    input  logic CLK,
    input  logic X,
    input  logic A_N,
    input  logic B_N,
    input  logic C,
    input  logic D
);
    // X high only when A_N=0, B_N=0, C=1, D=1.
    check_x_implies_inputs_ok: assert property (
        @(posedge CLK) X |-> (!A_N && !B_N && C && D)
    );

    // When A_N=0, B_N=0, C=1, D=1, X must be high.
    check_inputs_ok_implies_x: assert property (
        @(posedge CLK) (!A_N && !B_N && C && D) |-> X
    );

    // Any blocking condition (A_N=1 or B_N=1 or C=0 or D=0) forces X low.
    check_blocking_conditions_force_x_low: assert property (
        @(posedge CLK) (A_N || B_N || !C || !D) |-> !X
    );

    // With A_N=B_N=0 and C=1, X equals D.
    check_gate_open_x_eq_d: assert property (
        @(posedge CLK) (!A_N && !B_N && C) |-> (X == D)
    );

    // With A_N=B_N=0 and D=1, X equals C.
    check_gate_open_x_eq_c: assert property (
        @(posedge CLK) (!A_N && !B_N && D) |-> (X == C)
    );

    // With C=D=1, X equals (~A_N & ~B_N).
    check_cd_high_x_equals_nor_ab: assert property (
        @(posedge CLK) (C && D) |-> (X == (!A_N && !B_N))
    );

    // With gate open via C=1, a rising D sets X high.
    check_d_rise_sets_x_when_c_open: assert property (
        @(posedge CLK) ($rose(D) && !A_N && !B_N && C) |-> X
    );

    // With gate open via C=1, a falling D clears X low.
    check_d_fall_clears_x_when_c_open: assert property (
        @(posedge CLK) ($fell(D) && !A_N && !B_N && C) |-> !X
    );

    // With gate open via D=1, a rising C sets X high.
    check_c_rise_sets_x_when_d_open: assert property (
        @(posedge CLK) ($rose(C) && !A_N && !B_N && D) |-> X
    );

    // With gate open via D=1, a falling C clears X low.
    check_c_fall_clears_x_when_d_open: assert property (
        @(posedge CLK) ($fell(C) && !A_N && !B_N && D) |-> !X
    );
endmodule