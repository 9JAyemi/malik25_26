module mux4_1_sva (
    input logic clk,
    input logic [3:0] D0,
    input logic [3:0] D1,
    input logic [3:0] D2,
    input logic [3:0] D3,
    input logic S0,
    input logic S1,
    input logic [3:0] Y
);

    // Y always matches the implemented 4-to-1 mux expression.
    check_mux_function: assert property (
        @(posedge clk) Y === (S1 ? (S0 ? D3 : D2) : (S0 ? D1 : D0))
    );

    // Y routes D0 when the select value is 2'b00.
    check_select_00_routes_d0: assert property (
        @(posedge clk) ({S1, S0} === 2'b00) |-> (Y === D0)
    );

    // Y routes D1 when the select value is 2'b01.
    check_select_01_routes_d1: assert property (
        @(posedge clk) ({S1, S0} === 2'b01) |-> (Y === D1)
    );

    // Y routes D2 when the select value is 2'b10.
    check_select_10_routes_d2: assert property (
        @(posedge clk) ({S1, S0} === 2'b10) |-> (Y === D2)
    );

    // Y routes D3 when the select value is 2'b11.
    check_select_11_routes_d3: assert property (
        @(posedge clk) ({S1, S0} === 2'b11) |-> (Y === D3)
    );

endmodule