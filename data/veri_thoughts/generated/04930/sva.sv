module mux_2to1_sva (
    input logic A,
    input logic B,
    input logic S,
    input logic Y
);

    // Output matches the RTL mux equation.
    check_mux_equation: assert property (
        @($global_clock) Y === ((S == 1'b0) ? A : B)
    );

    // When select is low, output follows A.
    check_select_low_routes_a: assert property (
        @($global_clock) (S === 1'b0) |-> (Y === A)
    );

    // When select is high, output follows B.
    check_select_high_routes_b: assert property (
        @($global_clock) (S === 1'b1) |-> (Y === B)
    );

    // If both inputs are equal, output matches that value.
    check_equal_inputs_pass_through: assert property (
        @($global_clock) (A === B) |-> (Y === A)
    );

endmodule