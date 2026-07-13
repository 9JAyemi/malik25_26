module mux_4to1_sva (
    input logic CLK,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic S0,
    input logic S1,
    input logic Y
);
    // Y must equal the coded 4:1 mux equation.
    check_mux_equation: assert property (
        @(posedge CLK) Y == ((~S1 & ~S0 & A) | (~S1 & S0 & B) | (S1 & ~S0 & C) | (S1 & S0 & D))
    );

    // When S1S0==00, Y equals A.
    check_sel_00_maps_to_A: assert property (
        @(posedge CLK) (!S1 && !S0) |-> (Y == A)
    );

    // When S1S0==01, Y equals B.
    check_sel_01_maps_to_B: assert property (
        @(posedge CLK) (!S1 && S0) |-> (Y == B)
    );

    // When S1S0==10, Y equals C.
    check_sel_10_maps_to_C: assert property (
        @(posedge CLK) (S1 && !S0) |-> (Y == C)
    );

    // When S1S0==11, Y equals D.
    check_sel_11_maps_to_D: assert property (
        @(posedge CLK) (S1 && S0) |-> (Y == D)
    );

    // If A changes while selected and selects are stable, Y changes accordingly.
    check_A_change_reflects_Y: assert property (
        @(posedge CLK) ($stable(S1) && $stable(S0) && !S1 && !S0 && $changed(A)) |-> $changed(Y)
    );

    // If B changes while selected and selects are stable, Y changes accordingly.
    check_B_change_reflects_Y: assert property (
        @(posedge CLK) ($stable(S1) && $stable(S0) && !S1 && S0 && $changed(B)) |-> $changed(Y)
    );

    // If C changes while selected and selects are stable, Y changes accordingly.
    check_C_change_reflects_Y: assert property (
        @(posedge CLK) ($stable(S1) && $stable(S0) && S1 && !S0 && $changed(C)) |-> $changed(Y)
    );

    // If D changes while selected and selects are stable, Y changes accordingly.
    check_D_change_reflects_Y: assert property (
        @(posedge CLK) ($stable(S1) && $stable(S0) && S1 && S0 && $changed(D)) |-> $changed(Y)
    );
endmodule