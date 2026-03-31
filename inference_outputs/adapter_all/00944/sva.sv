module mux4_1_sva (
    input logic clk,
    input logic Y,
    input logic D0,
    input logic D1,
    input logic D2,
    input logic D3,
    input logic S0,
    input logic S1,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // Y must match the 4-to-1 mux function.
    check_mux_function: assert property (
        @(posedge clk)
        Y == (S1 ? (S0 ? D3 : D2) : (S0 ? D1 : D0))
    );

    // When S1 is low, Y selects between D0 and D1.
    check_select_low_path: assert property (
        @(posedge clk)
        !S1 |-> (Y == (S0 ? D1 : D0))
    );

    // When S1 is high, Y selects between D2 and D3.
    check_select_high_path: assert property (
        @(posedge clk)
        S1 |-> (Y == (S0 ? D3 : D2))
    );

    // With S1 low and S0 low, Y must equal D0.
    check_select_00: assert property (
        @(posedge clk)
        (!S1 && !S0) |-> (Y == D0)
    );

    // With S1 low and S0 high, Y must equal D1.
    check_select_01: assert property (
        @(posedge clk)
        (!S1 && S0) |-> (Y == D1)
    );

    // With S1 high and S0 low, Y must equal D2.
    check_select_10: assert property (
        @(posedge clk)
        (S1 && !S0) |-> (Y == D2)
    );

    // With S1 high and S0 high, Y must equal D3.
    check_select_11: assert property (
        @(posedge clk)
        (S1 && S0) |-> (Y == D3)
    );

    // With S1 low, a change on S0 must change Y between D0 and D1.
    check_select_low_s0_change: assert property (
        @(posedge clk)
        (!S1 && $changed(S0)) |-> (Y == (S0 ? D1 : D0))
    );

    // With S1 high, a change on S0 must change Y between D2 and D3.
    check_select_high_s0_change: assert property (
        @(posedge clk)
        (S1 && $changed(S0)) |-> (Y == (S0 ? D3 : D2))
    );

    // With S0 low, a change on S1 must change Y between D0 and D2.
    check_select_low_s1_change: assert property (
        @(posedge clk)
        (!S0 && $changed(S1)) |-> (Y == (S1 ? D2 : D0))
    );

    // With S0 high, a change on S1 must change Y between D1 and D3.
    check_select_high_s1_change: assert property (
        @(posedge clk)
        (S0 && $changed(S1)) |-> (Y == (S1 ? D3 : D1))
    );

endmodule