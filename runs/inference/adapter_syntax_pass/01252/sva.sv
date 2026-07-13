module inverter_sva (
    input logic clk,
    input logic I,
    input logic O
);
    // O must always be the logical inverse of I.
    check_inverter_function: assert property (
        @(posedge clk) O == ~I
    );

    // A rising I must cause a falling O.
    check_inverter_rise_I_fall_O: assert property (
        @(posedge clk) $rose(I) |-> $fell(O)
    );

    // A falling I must cause a rising O.
    check_inverter_fall_I_rise_O: assert property (
        @(posedge clk) $fell(I) |-> $rose(O)
    );

    // O must never equal I.
    check_inverter_never_equal: assert property (
        @(posedge clk) O != I
    );
endmodule

module and_gate_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic Y
);
    // Y must always equal A & B.
    check_and_function: assert property (
        @(posedge clk) Y == (A & B)
    );

    // A rising Y must imply both A and B are HIGH.
    check_and_rise_Y_requires_A_and_B: assert property (
        @(posedge clk) $rose(Y) |-> (A && B)
    );

    // A falling Y must imply at least one input is LOW.
    check_and_fall_Y_requires_not_A_or_not_B: assert property (
        @(posedge clk) $fell(Y) |-> (!A || !B)
    );

    // A rising A must cause a rising Y when B is HIGH.
    check_and_rise_A_causes_rise_Y_when_B_high: assert property (
        @(posedge clk) ($rose(A) && B) |-> $rose(Y)
    );

    // A falling A must cause a falling Y.
    check_and_fall_A_causes_fall_Y: assert property (
        @(posedge clk) $fell(A) |-> $fell(Y)
    );

    // A rising B must cause a rising Y when A is HIGH.
    check_and_rise_B_causes_rise_Y_when_A_high: assert property (
        @(posedge clk) ($rose(B) && A) |-> $rose(Y)
    );

    // A falling B must cause a falling Y.
    check_and_fall_B_causes_fall_Y: assert property (
        @(posedge clk) $fell(B) |-> $fell(Y)
    );
endmodule

module mux_2to1_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic S,
    input logic Y
);
    // Y must equal A when S is LOW.
    check_mux_select_A_when_S_low: assert property (
        @(posedge clk) (S == 1'b0) |-> (Y == A)
    );

    // Y must equal B when S is HIGH.
    check_mux_select_B_when_S_high: assert property (
        @(posedge clk) (S == 1'b1) |-> (Y == B)
    );

    // A rising S must cause Y to equal B.
    check_mux_rise_S_selects_B: assert property (
        @(posedge clk) $rose(S) |-> (Y == B)
    );

    // A falling S must cause Y to equal A.
    check_mux_fall_S_selects_A: assert property (
        @(posedge clk) $fell(S) |-> (Y == A)
    );

    // With S LOW and A stable, a change on B must not affect Y.
    check_mux_S_low_A_stable_B_change_no_effect: assert property (
        @(posedge clk) (S == 1'b0 && $stable(S) && $stable(A) && $changed(B)) |-> $stable(Y)
    );

    // With S HIGH and B stable, a change on A must not affect Y.
    check_mux_S_high_B_stable_A_change_no_effect: assert property (
        @(posedge clk) (S == 1'b1 && $stable(S) && $stable(B) && $changed(A)) |-> $stable(Y)
    );
endmodule