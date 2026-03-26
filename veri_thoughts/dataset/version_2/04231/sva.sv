module mux2to1_sva(
    input logic clk,
    input logic A,
    input logic B,
    input logic S,
    input logic Y
);

    // DUT is combinational; clk is only for assertion sampling.
    // Output must always match the RTL mux equation.
    check_mux_function_exact: assert property (
        @(posedge clk) (Y === ((S == 1'b0) ? A : B))
    );

    // When select is 0, output must match A.
    check_select_low_routes_a: assert property (
        @(posedge clk) (S === 1'b0) |-> (Y === A)
    );

    // When select is 1, output must match B.
    check_select_high_routes_b: assert property (
        @(posedge clk) (S === 1'b1) |-> (Y === B)
    );

    // Equal inputs must force the same output regardless of select.
    check_equal_inputs_force_output: assert property (
        @(posedge clk) (A === B) |-> (Y === A)
    );

    // Unknown select with different inputs must produce an unknown output.
    check_unknown_select_diff_inputs_x_output: assert property (
        @(posedge clk) ($isunknown(S) && (A !== B)) |-> $isunknown(Y)
    );

endmodule