module mux_2to1_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic S,
    input logic Y
);

    // Output must match the implemented ternary mux expression.
    check_mux_function: assert property (
        @(posedge clk) Y === ((S == 1'b0) ? A : B)
    );

    // Select value 0 routes input A to the output.
    check_select_zero_routes_a: assert property (
        @(posedge clk) (S === 1'b0) |-> (Y === A)
    );

    // Select value 1 routes input B to the output.
    check_select_one_routes_b: assert property (
        @(posedge clk) (S === 1'b1) |-> (Y === B)
    );

    // Equal data inputs force the same value at the output.
    check_equal_inputs_propagate: assert property (
        @(posedge clk) (A === B) |-> (Y === A)
    );

    // Stable mux inputs keep the output stable.
    check_stable_inputs_keep_output_stable: assert property (
        @(posedge clk) ($stable(A) && $stable(B) && $stable(S)) |-> $stable(Y)
    );

endmodule