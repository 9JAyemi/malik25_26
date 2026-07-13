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

    // Y must match the muxed 4-to-1 function when enabled.
    check_mux_function: assert property (
        @(posedge clk) disable iff (1'b0)
        EN |-> (Y == (SEL[1] ? (SEL[0] ? D3 : D2) : (SEL[0] ? D1 : D0)))
    );

    // When disabled, Y must be high-impedance.
    check_disable_highz: assert property (
        @(posedge clk) disable iff (1'b0)
        !EN |-> (Y == 1'bz)
    );

    // With SEL=00 and enabled, Y must select D0.
    check_sel_00: assert property (
        @(posedge clk) disable iff (1'b0)
        (EN && (SEL == 2'b00)) |-> (Y == D0)
    );

    // With SEL=01 and enabled, Y must select D1.
    check_sel_01: assert property (
        @(posedge clk) disable iff (1'b0)
        (EN && (SEL == 2'b01)) |-> (Y == D1)
    );

    // With SEL=10 and enabled, Y must select D2.
    check_sel_10: assert property (
        @(posedge clk) disable iff (1'b0)
        (EN && (SEL == 2'b10)) |-> (Y == D2)
    );

    // With SEL=11 and enabled, Y must select D3.
    check_sel_11: assert property (
        @(posedge clk) disable iff (1'b0)
        (EN && (SEL == 2'b11)) |-> (Y == D3)
    );

endmodule