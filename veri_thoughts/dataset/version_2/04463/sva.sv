module mux_4to2_sva (
    input logic clk,
    input logic [3:0] A0,
    input logic [3:0] A1,
    input logic [3:0] A2,
    input logic [3:0] A3,
    input logic S0,
    input logic S1,
    input logic [3:0] X
);

    // External sampling clock; the RTL itself has no clock or reset.

    // X must match A0 when the select is 00.
    check_select_a0: assert property (
        @(posedge clk) ({S1, S0} == 2'b00) |-> (X == A0)
    );

    // X must match A1 when the select is 01.
    check_select_a1: assert property (
        @(posedge clk) ({S1, S0} == 2'b01) |-> (X == A1)
    );

    // X must match A2 when the select is 10.
    check_select_a2: assert property (
        @(posedge clk) ({S1, S0} == 2'b10) |-> (X == A2)
    );

    // X must match A3 when the select is 11.
    check_select_a3: assert property (
        @(posedge clk) ({S1, S0} == 2'b11) |-> (X == A3)
    );

endmodule