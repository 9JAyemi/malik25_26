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

    // Y must match the enabled 4-to-1 mux function.
    check_mux_function: assert property (
        @(posedge clk) disable iff (1'b0)
        Y == (EN ? (SEL[1] ? (SEL[0] ? D3 : D2) : (SEL[0] ? D1 : D0)) : 1'b0)
    );

    // When disabled, Y must be low.
    check_disabled_low: assert property (
        @(posedge clk) disable iff (1'b0)
        !EN |-> (Y == 1'b0)
    );

    // With SEL=00, Y must select D0 when enabled.
    check_sel_00_selects_d0: assert property (
        @(posedge clk) disable iff (1'b0)
        (EN && (SEL == 2'b00)) |-> (Y == D0)
    );

    // With SEL=01, Y must select D1 when enabled.
    check_sel_01_selects_d1: assert property (
        @(posedge clk) disable iff (1'b0)
        (EN && (SEL == 2'b01)) |-> (Y == D1)
    );

    // With SEL=10, Y must select D2 when enabled.
    check_sel_10_selects_d2: assert property (
        @(posedge clk) disable iff (1'b0)
        (EN && (SEL == 2'b10)) |-> (Y == D2)
    );

    // With SEL=11, Y must select D3 when enabled.
    check_sel_11_selects_d3: assert property (
        @(posedge clk) disable iff (1'b0)
        (EN && (SEL == 2'b11)) |-> (Y == D3)
    );

endmodule