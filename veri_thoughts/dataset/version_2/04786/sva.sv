module Multiplexer_AC__parameterized94_sva (
    input logic clk,
    input logic ctrl,
    input logic [0:0] D0,
    input logic [0:0] D1,
    input logic [0:0] S
);

    // When ctrl is low, the output selects D0.
    check_select_d0: assert property (
        @(posedge clk) !ctrl |-> (S === D0)
    );

    // When ctrl is high, the output selects D1.
    check_select_d1: assert property (
        @(posedge clk) ctrl |-> (S === D1)
    );

    // The output always matches the mux equation.
    check_mux_equation: assert property (
        @(posedge clk) (S === (ctrl ? D1 : D0))
    );

    // If both data inputs are equal, the output matches that common value.
    check_equal_inputs_pass_through: assert property (
        @(posedge clk) (D0 === D1) |-> (S === D0)
    );

endmodule