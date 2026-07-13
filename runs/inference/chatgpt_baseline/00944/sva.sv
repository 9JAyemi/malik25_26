module mux4_1_sva (
    input logic CLK,          // sampling clock for assertions (RTL has no clock/reset)
    input logic Y,
    input logic D0, D1, D2, D3, S0, S1, VPWR, VGND, VPB, VNB
);
    // Route Y = D0 when S1=0,S0=0 and selects are known.
    route_sel00_to_D0: assert property (
        @(posedge CLK) (!$isunknown(S0) && !$isunknown(S1) && (S1==1'b0) && (S0==1'b0)) |-> (Y === D0)
    );
    // Route Y = D1 when S1=0,S0=1 and selects are known.
    route_sel01_to_D1: assert property (
        @(posedge CLK) (!$isunknown(S0) && !$isunknown(S1) && (S1==1'b0) && (S0==1'b1)) |-> (Y === D1)
    );
    // Route Y = D2 when S1=1,S0=0 and selects are known.
    route_sel10_to_D2: assert property (
        @(posedge CLK) (!$isunknown(S0) && !$isunknown(S1) && (S1==1'b1) && (S0==1'b0)) |-> (Y === D2)
    );
    // Route Y = D3 when S1=1,S0=1 and selects are known.
    route_sel11_to_D3: assert property (
        @(posedge CLK) (!$isunknown(S0) && !$isunknown(S1) && (S1==1'b1) && (S0==1'b1)) |-> (Y === D3)
    );

    // Any unknown on S0 or S1 must drive Y to X (due to default in mux2_1).
    xprop_when_select_unknown: assert property (
        @(posedge CLK) ($isunknown(S0) || $isunknown(S1)) |-> (Y === 1'bx)
    );

    // If all inputs and selects are stable, Y must be stable (purely combinational).
    stable_inputs_hold_output: assert property (
        @(posedge CLK) (!$changed(D0) && !$changed(D1) && !$changed(D2) && !$changed(D3) && !$changed(S0) && !$changed(S1)) |-> !$changed(Y)
    );

    // With S1=0 and S1/S0/D0/D1 stable, Y does not change regardless of D2/D3.
    s1_low_lower_half_independence: assert property (
        @(posedge CLK) ((S1==1'b0) && !$changed(S1) && !$changed(S0) && !$changed(D0) && !$changed(D1)) |-> !$changed(Y)
    );

    // With S1=1 and S1/S0/D2/D3 stable, Y does not change regardless of D0/D1.
    s1_high_upper_half_independence: assert property (
        @(posedge CLK) ((S1==1'b1) && !$changed(S1) && !$changed(S0) && !$changed(D2) && !$changed(D3)) |-> !$changed(Y)
    );

    // When S1=0 and D0!=D1 (known, stable), a toggle on S0 must toggle Y.
    s0_toggle_changes_output_when_s1_low: assert property (
        @(posedge CLK)
        ((S1==1'b0) && !$isunknown(S1) &&
         !$isunknown(S0) && !$isunknown($past(S0)) &&
         !$changed(S1) && $changed(S0) &&
         !$changed(D0) && !$changed(D1) &&
         !$isunknown(D0) && !$isunknown(D1) &&
         (D0 !== D1)) |-> $changed(Y)
    );

    // When S1=1 and D2!=D3 (known, stable), a toggle on S0 must toggle Y.
    s0_toggle_changes_output_when_s1_high: assert property (
        @(posedge CLK)
        ((S1==1'b1) && !$isunknown(S1) &&
         !$isunknown(S0) && !$isunknown($past(S0)) &&
         !$changed(S1) && $changed(S0) &&
         !$changed(D2) && !$changed(D3) &&
         !$isunknown(D2) && !$isunknown(D3) &&
         (D2 !== D3)) |-> $changed(Y)
    );
endmodule