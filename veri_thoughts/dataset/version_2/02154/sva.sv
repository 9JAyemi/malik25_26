module mux4to1_sva (
    input logic CLK,
    input logic RESETn,
    input logic A, B, C, D,
    input logic S0, S1,
    input logic Y
);
    // Y implements the 4:1 mux boolean function of selects and data.
    check_mux_function: assert property (
        @(posedge CLK) disable iff (!RESETn)
        Y == ((~S1 & ~S0 & A) | (~S1 & S0 & B) | (S1 & ~S0 & C) | (S1 & S0 & D))
    );

    // When S1S0=00, Y equals A.
    check_sel00_routes_A: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (S1==1'b0 && S0==1'b0) |-> (Y == A)
    );

    // When S1S0=01, Y equals B.
    check_sel01_routes_B: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (S1==1'b0 && S0==1'b1) |-> (Y == B)
    );

    // When S1S0=10, Y equals C.
    check_sel10_routes_C: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (S1==1'b1 && S0==1'b0) |-> (Y == C)
    );

    // When S1S0=11, Y equals D.
    check_sel11_routes_D: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (S1==1'b1 && S0==1'b1) |-> (Y == D)
    );

    // With S1S0 held at 00 and other inputs stable, Y changes iff A changes.
    track_A_when_sel00: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (S1==1'b0 && S0==1'b0 && $stable(S1) && $stable(S0) && $stable(B) && $stable(C) && $stable(D))
        |-> ($changed(Y) == $changed(A))
    );

    // With S1S0 held at 01 and other inputs stable, Y changes iff B changes.
    track_B_when_sel01: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (S1==1'b0 && S0==1'b1 && $stable(S1) && $stable(S0) && $stable(A) && $stable(C) && $stable(D))
        |-> ($changed(Y) == $changed(B))
    );

    // With S1S0 held at 10 and other inputs stable, Y changes iff C changes.
    track_C_when_sel10: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (S1==1'b1 && S0==1'b0 && $stable(S1) && $stable(S0) && $stable(A) && $stable(B) && $stable(D))
        |-> ($changed(Y) == $changed(C))
    );

    // With S1S0 held at 11 and other inputs stable, Y changes iff D changes.
    track_D_when_sel11: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (S1==1'b1 && S0==1'b1 && $stable(S1) && $stable(S0) && $stable(A) && $stable(B) && $stable(C))
        |-> ($changed(Y) == $changed(D))
    );

    // If all inputs and selects are stable, Y must remain stable.
    stable_inputs_hold_Y: assert property (
        @(posedge CLK) disable iff (!RESETn)
        $stable({A,B,C,D,S0,S1}) |-> $stable(Y)
    );
endmodule