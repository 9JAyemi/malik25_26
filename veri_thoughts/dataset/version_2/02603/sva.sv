module mux_4to1_sva (
    input logic clk,
    input logic reset_n,
    input logic [7:0] D0,
    input logic [7:0] D1,
    input logic [7:0] D2,
    input logic [7:0] D3,
    input logic [1:0] SEL,
    input logic [7:0] Y
);
    // When SEL==00, Y equals D0 in the same cycle.
    check_sel00_maps_d0: assert property (
        @(posedge clk) disable iff (!reset_n) (SEL == 2'b00) |-> (Y == D0)
    );

    // When SEL==01, Y equals D1 in the same cycle.
    check_sel01_maps_d1: assert property (
        @(posedge clk) disable iff (!reset_n) (SEL == 2'b01) |-> (Y == D1)
    );

    // When SEL==10, Y equals D2 in the same cycle.
    check_sel10_maps_d2: assert property (
        @(posedge clk) disable iff (!reset_n) (SEL == 2'b10) |-> (Y == D2)
    );

    // When SEL==11, Y equals D3 in the same cycle.
    check_sel11_maps_d3: assert property (
        @(posedge clk) disable iff (!reset_n) (SEL == 2'b11) |-> (Y == D3)
    );

    // Functional equivalence to a 4:1 mux tree driven by SEL bits.
    check_mux_function: assert property (
        @(posedge clk) disable iff (!reset_n) Y == (SEL[1] ? (SEL[0] ? D3 : D2) : (SEL[0] ? D1 : D0))
    );

    // With SEL==00 held and D0 stable across a cycle, Y must be stable.
    check_stability_sel00: assert property (
        @(posedge clk) disable iff (!reset_n) (SEL == 2'b00 && $stable(SEL) && $stable(D0)) |-> $stable(Y)
    );

    // With SEL==01 held and D1 stable across a cycle, Y must be stable.
    check_stability_sel01: assert property (
        @(posedge clk) disable iff (!reset_n) (SEL == 2'b01 && $stable(SEL) && $stable(D1)) |-> $stable(Y)
    );

    // With SEL==10 held and D2 stable across a cycle, Y must be stable.
    check_stability_sel10: assert property (
        @(posedge clk) disable iff (!reset_n) (SEL == 2'b10 && $stable(SEL) && $stable(D2)) |-> $stable(Y)
    );

    // With SEL==11 held and D3 stable across a cycle, Y must be stable.
    check_stability_sel11: assert property (
        @(posedge clk) disable iff (!reset_n) (SEL == 2'b11 && $stable(SEL) && $stable(D3)) |-> $stable(Y)
    );
endmodule