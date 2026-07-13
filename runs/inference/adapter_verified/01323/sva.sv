module Multiplexer_sva (
    input logic clk,
    input logic ctrl,
    input logic [31:0] D0,
    input logic [31:0] D1,
    input logic [31:0] S
);

// S must match the RTL mux equation.
    check_mux_equation: assert property (
        @(posedge clk) S == (ctrl ? D1 : D0)
    );

// When ctrl is 0, S must equal D0.
    check_select_d0: assert property (
        @(posedge clk) !ctrl |-> (S == D0)
    );

// When ctrl is 1, S must equal D1.
    check_select_d1: assert property (
        @(posedge clk) ctrl |-> (S == D1)
    );

// If both data inputs are equal, S must equal that value regardless of ctrl.
    check_equal_inputs_passthrough: assert property (
        @(posedge clk) (D0 == D1) |-> (S == D0)
    );

endmodule
