module mux4to1_sva (
    input logic CLK,
    input logic Y,
    input logic D0,
    input logic D1,
    input logic D2,
    input logic D3,
    input logic S0,
    input logic S1
);
    // Y equals D0 when S0=0 and S1=0.
    select_00_maps_to_D0: assert property (
        @(posedge CLK) ((S0 == 1'b0) && (S1 == 1'b0)) |-> (Y == D0)
    );

    // Y equals D1 when S0=0 and S1=1.
    select_01_maps_to_D1: assert property (
        @(posedge CLK) ((S0 == 1'b0) && (S1 == 1'b1)) |-> (Y == D1)
    );

    // Y equals D2 when S0=1 and S1=0.
    select_10_maps_to_D2: assert property (
        @(posedge CLK) ((S0 == 1'b1) && (S1 == 1'b0)) |-> (Y == D2)
    );

    // Y equals D3 when S0=1 and S1=1.
    select_11_maps_to_D3: assert property (
        @(posedge CLK) ((S0 == 1'b1) && (S1 == 1'b1)) |-> (Y == D3)
    );

    // Y matches the nested 2:1 mux composition.
    function_equivalence_nested_mux: assert property (
        @(posedge CLK) Y == (S0 ? (S1 ? D3 : D2) : (S1 ? D1 : D0))
    );

    // If all data and selects are stable, Y remains stable (purely combinational).
    stability_when_inputs_stable: assert property (
        @(posedge CLK) $stable({D0,D1,D2,D3,S0,S1}) |-> $stable(Y)
    );

    // With S0=0,S1=0 held stable, a change on D0 causes a corresponding change on Y.
    change_propagation_00: assert property (
        @(posedge CLK) ($stable(S0) && $stable(S1) && (S0 == 1'b0) && (S1 == 1'b0) && $changed(D0)) |-> ($changed(Y) && (Y == D0))
    );

    // With S0=0,S1=1 held stable, a change on D1 causes a corresponding change on Y.
    change_propagation_01: assert property (
        @(posedge CLK) ($stable(S0) && $stable(S1) && (S0 == 1'b0) && (S1 == 1'b1) && $changed(D1)) |-> ($changed(Y) && (Y == D1))
    );

    // With S0=1,S1=0 held stable, a change on D2 causes a corresponding change on Y.
    change_propagation_10: assert property (
        @(posedge CLK) ($stable(S0) && $stable(S1) && (S0 == 1'b1) && (S1 == 1'b0) && $changed(D2)) |-> ($changed(Y) && (Y == D2))
    );

    // With S0=1,S1=1 held stable, a change on D3 causes a corresponding change on Y.
    change_propagation_11: assert property (
        @(posedge CLK) ($stable(S0) && $stable(S1) && (S0 == 1'b1) && (S1 == 1'b1) && $changed(D3)) |-> ($changed(Y) && (Y == D3))
    );
endmodule