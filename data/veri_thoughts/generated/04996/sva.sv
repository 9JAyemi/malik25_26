module mux_4to2_en_sva (
    input logic clk,
    input logic A0,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic S0,
    input logic S1,
    input logic EN,
    input logic X
);

    // X must be low whenever the mux is disabled.
    check_x_low_when_disabled: assert property (
        @(posedge clk) !EN |-> (X == 1'b0)
    );

    // When enabled with S1S0=00, X must select A2.
    check_select_00_routes_a2: assert property (
        @(posedge clk) EN && !S1 && !S0 |-> (X == A2)
    );

    // When enabled with S1S0=01, X must select A0.
    check_select_01_routes_a0: assert property (
        @(posedge clk) EN && !S1 && S0 |-> (X == A0)
    );

    // When enabled with S1S0=10, X must select A1.
    check_select_10_routes_a1: assert property (
        @(posedge clk) EN && S1 && !S0 |-> (X == A1)
    );

    // When enabled with S1S0=11, X must select A3.
    check_select_11_routes_a3: assert property (
        @(posedge clk) EN && S1 && S0 |-> (X == A3)
    );

endmodule