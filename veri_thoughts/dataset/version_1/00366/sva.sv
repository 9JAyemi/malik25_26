module Multiplexer_AC__parameterized57_sva (
    input logic clk,
    input logic ctrl,
    input logic [0:0] D0,
    input logic [0:0] D1,
    input logic [0:0] S
);

    // S must select D0 when ctrl is low.
    check_select_d0: assert property (
        @(posedge clk) !ctrl |-> (S == D0)
    );

    // S must select D1 when ctrl is high.
    check_select_d1: assert property (
        @(posedge clk) ctrl |-> (S == D1)
    );

    // S must always match the RTL mux equation.
    check_mux_equation: assert property (
        @(posedge clk) S == (ctrl ? D1 : D0)
    );

endmodule