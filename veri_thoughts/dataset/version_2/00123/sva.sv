module mux_4_to_1_sva (
    input logic D0,
    input logic D1,
    input logic D2,
    input logic D3,
    input logic S0,
    input logic S1,
    input logic Y
);

    // Select 00 routes D0 to Y.
    check_select_00_routes_d0: assert property (
        @($global_clock) ({S1, S0} === 2'b00) |-> (Y === D0)
    );

    // Select 01 routes D1 to Y.
    check_select_01_routes_d1: assert property (
        @($global_clock) ({S1, S0} === 2'b01) |-> (Y === D1)
    );

    // Select 10 routes D2 to Y.
    check_select_10_routes_d2: assert property (
        @($global_clock) ({S1, S0} === 2'b10) |-> (Y === D2)
    );

    // Select 11 routes D3 to Y.
    check_select_11_routes_d3: assert property (
        @($global_clock) ({S1, S0} === 2'b11) |-> (Y === D3)
    );

endmodule