module mux_4to1_sva (
    input logic clk,
    input logic Y,
    input logic D0,
    input logic D1,
    input logic D2,
    input logic D3,
    input logic [1:0] SEL,
    input logic EN
);

// Y matches the 4-to-1 mux equation when enabled.
    check_mux_function: assert property (
        @(posedge clk) EN |-> (Y == ((~SEL[1] & SEL[0] & D0) | (SEL[1] & SEL[0] & D1) | (~SEL[1] & ~SEL[0] & D2) | (SEL[1] & ~SEL[0] & D3)))
    );

// When disabled, Y is forced low.
    check_disabled_forces_low: assert property (
        @(posedge clk) !EN |-> (Y == 1'b0)
    );

// With SEL==2'b00, Y follows D2 when enabled.
    check_sel_00_routes_d2: assert property (
        @(posedge clk) (SEL == 2'b00 && EN) |-> (Y == D2)
    );

// With SEL==2'b01, Y follows D0 when enabled.
    check_sel_01_routes_d0: assert property (
        @(posedge clk) (SEL == 2'b01 && EN) |-> (Y == D0)
    );

// With SEL==2'b10, Y follows D3 when enabled.
    check_sel_10_routes_d3: assert property (
        @(posedge clk) (SEL == 2'b10 && EN) |-> (Y == D3)
    );

// With SEL==2'b11, Y follows D1 when enabled.
    check_sel_11_routes_d1: assert property (
        @(posedge clk) (SEL == 2'b11 && EN) |-> (Y == D1)
    );

endmodule
