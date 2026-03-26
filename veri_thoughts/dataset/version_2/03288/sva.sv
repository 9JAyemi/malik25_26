module mux_2to1_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic S,
    input logic Y
);

    // Output always matches the implemented mux equation.
    check_output_matches_mux_equation: assert property (
        @(posedge clk) Y === ((S == 1'b0) ? A : B)
    );

    // When select is 0, output follows A.
    check_select_zero_routes_a: assert property (
        @(posedge clk) (S === 1'b0) |-> (Y === A)
    );

    // When select is 1, output follows B.
    check_select_one_routes_b: assert property (
        @(posedge clk) (S === 1'b1) |-> (Y === B)
    );

    // If both inputs are equal, output matches that common value.
    check_equal_inputs_propagate: assert property (
        @(posedge clk) (A === B) |-> (Y === A)
    );

endmodule