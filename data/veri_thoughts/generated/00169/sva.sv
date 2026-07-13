module mux17_sva(
    input logic [16:0] A,
    input logic [16:0] B,
    input logic S,
    input logic [16:0] MO
);

    // Output matches the RTL mux expression.
    check_mux_expression: assert property (
        @($global_clock) MO === ((S == 1'b1) ? B : A)
    );

    // When select is high, output follows B.
    check_select_high_routes_b: assert property (
        @($global_clock) (S === 1'b1) |-> (MO === B)
    );

    // When select is low, output follows A.
    check_select_low_routes_a: assert property (
        @($global_clock) (S === 1'b0) |-> (MO === A)
    );

    // If both inputs are equal, output matches that value.
    check_equal_inputs_passthrough: assert property (
        @($global_clock) (A === B) |-> (MO === A)
    );

    // With B selected and stable, output stays stable.
    check_stable_b_keeps_output_stable: assert property (
        @($global_clock) ((S === 1'b1) && $stable(S) && $stable(B)) |-> $stable(MO)
    );

    // With A selected and stable, output stays stable.
    check_stable_a_keeps_output_stable: assert property (
        @($global_clock) ((S === 1'b0) && $stable(S) && $stable(A)) |-> $stable(MO)
    );

endmodule