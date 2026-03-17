module Multiplexer_sva
    #(parameter N = 1)
    (
        input logic clk,
        input logic [N-1:0] D0,
        input logic [N-1:0] D1,
        input logic ctrl,
        input logic [N-1:0] S
    );

    // S follows D0 when ctrl is low.
    check_select_d0: assert property (
        @(posedge clk) disable iff (1'b0) !ctrl |-> (S == D0)
    );

    // S follows D1 when ctrl is high.
    check_select_d1: assert property (
        @(posedge clk) disable iff (1'b0) ctrl |-> (S == D1)
    );

    // S always matches the mux select expression.
    check_mux_equation: assert property (
        @(posedge clk) disable iff (1'b0) S == (ctrl ? D1 : D0)
    );

    // If both inputs are equal, S matches that common value.
    check_equal_inputs_passthrough: assert property (
        @(posedge clk) disable iff (1'b0) (D0 == D1) |-> (S == D0)
    );

endmodule