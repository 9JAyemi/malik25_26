module mux2to1_sva (
    input logic        clk,
    input logic [3:0]  in0,
    input logic [3:0]  in1,
    input logic        ctrl,
    input logic [3:0]  out
);

    // The sampled output must always match the RTL mux expression.
    check_mux_function: assert property (
        @(posedge clk) out === ((ctrl == 1'b0) ? in0 : in1)
    );

    // When control is low, the output selects in0.
    check_select_in0: assert property (
        @(posedge clk) (ctrl === 1'b0) |-> (out === in0)
    );

    // When control is high, the output selects in1.
    check_select_in1: assert property (
        @(posedge clk) (ctrl === 1'b1) |-> (out === in1)
    );

    // If both inputs are identical, the output must match that value.
    check_equal_inputs_passthrough: assert property (
        @(posedge clk) (in0 === in1) |-> (out === in0)
    );

endmodule