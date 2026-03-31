module mux_2_1_sva (
    input logic clk,
    input logic sel,
    input logic in0,
    input logic in1,
    input logic out
);

    // Output must match the implemented mux equation.
    check_mux_equation: assert property (
        @(posedge clk) out == ((in0 & ~sel) | (in1 & sel))
    );

    // When select is low, the output must follow in0.
    check_select_low_routes_in0: assert property (
        @(posedge clk) !sel |-> (out == in0)
    );

    // When select is high, the output must follow in1.
    check_select_high_routes_in1: assert property (
        @(posedge clk) sel |-> (out == in1)
    );

    // With select low and both inputs equal, the output must match that value.
    check_equal_inputs_select_low: assert property (
        @(posedge clk) (!sel && (in0 == in1)) |-> (out == in0)
    );

    // With select high and both inputs equal, the output must match that value.
    check_equal_inputs_select_high: assert property (
        @(posedge clk) (sel && (in0 == in1)) |-> (out == in0)
    );

    // With select low and different inputs, the output must be the inverse of in0.
    check_different_inputs_select_low: assert property (
        @(posedge clk) (!sel && (in0 != in1)) |-> (out == ~in0)
    );

    // With select high and different inputs, the output must be the inverse of in1.
    check_different_inputs_select_high: assert property (
        @(posedge clk) (sel && (in0 != in1)) |-> (out == ~in1)
    );

endmodule