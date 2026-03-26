module Multiplexer_AC__parameterized137_sva (
    input logic clk,
    input logic ctrl,
    input logic [0:0] D0,
    input logic [0:0] D1,
    input logic [0:0] S
);

    // Output always matches the mux select expression.
    check_mux_function: assert property (
        @(posedge clk) S == (ctrl ? D1 : D0)
    );

    // Low control selects D0.
    check_select_d0: assert property (
        @(posedge clk) !ctrl |-> (S == D0)
    );

    // High control selects D1.
    check_select_d1: assert property (
        @(posedge clk) ctrl |-> (S == D1)
    );

    // Equal data inputs force the output to that common value.
    check_equal_inputs: assert property (
        @(posedge clk) (D0 == D1) |-> (S == D0)
    );

endmodule