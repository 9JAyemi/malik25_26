module mux4_1_sva (
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

    // Y must match the implemented mux equation.
    check_output_matches_mux_equation: assert property (
        @($global_clock)
        Y == (S1 ? (S0 ? D3 : D2) : (S0 ? D1 : D0))
    );

    // When S1 is low, Y must select between D0 and D1.
    check_select0_path: assert property (
        @($global_clock)
        !S1 |-> (Y == (S0 ? D1 : D0))
    );

    // When S1 is high, Y must select between D2 and D3.
    check_select1_path: assert property (
        @($global_clock)
        S1 |-> (Y == (S0 ? D3 : D2))
    );

    // When S0 is low, Y must select D0 regardless of S1.
    check_select0_low_selects_d0: assert property (
        @($global_clock)
        !S0 |-> (Y == D0)
    );

    // When S0 is high, Y must select D1 regardless of S1.
    check_select0_high_selects_d1: assert property (
        @($global_clock)
        S0 |-> (Y == D1)
    );

    // With S1 low and S0 low, Y must equal D0.
    check_select00_selects_d0: assert property (
        @($global_clock)
        (!S1 && !S0) |-> (Y == D0)
    );

    // With S1 low and S0 high, Y must equal D1.
    check_select01_selects_d1: assert property (
        @($global_clock)
        (!S1 && S0) |-> (Y == D1)
    );

    // With S1 high and S0 low, Y must equal D2.
    check_select10_selects_d2: assert property (
        @($global_clock)
        (S1 && !S0) |-> (Y == D2)
    );

    // With S1 high and S0 high, Y must equal D3.
    check_select11_selects_d3: assert property (
        @($global_clock)
        (S1 && S0) |-> (Y == D3)
    );

endmodule