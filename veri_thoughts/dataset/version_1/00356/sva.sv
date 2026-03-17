module Multiplexer_2_1_parameterized1_sva (
    input logic clk,
    input logic ctrl,
    input logic [0:0] D0,
    input logic [0:0] D1,
    input logic [0:0] S
);

    // Output must match the implemented mux equation.
    check_mux_equation: assert property (
        @(posedge clk) S === ((ctrl == 1'b0) ? D0 : D1)
    );

    // ctrl low selects D0.
    check_select_d0_when_ctrl_low: assert property (
        @(posedge clk) (ctrl === 1'b0) |-> (S === D0)
    );

    // ctrl high selects D1.
    check_select_d1_when_ctrl_high: assert property (
        @(posedge clk) (ctrl === 1'b1) |-> (S === D1)
    );

    // When both inputs match, the output matches them as well.
    check_equal_inputs_produce_same_output: assert property (
        @(posedge clk) (D0 === D1) |-> (S === D0)
    );

endmodule